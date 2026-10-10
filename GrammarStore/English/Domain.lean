import GrammarStore.Store
import GrammarStore.English.Morphology

/-!
# English past tense as a grammar-store domain

## Queries
Every question a rule may ask is keyed, so a cached answer's label names
exactly what it relied on:

* `verb b`     — the lexical status of lemma `b`: irregular entry, regular, or absent.
* `readings w` — the lemmas whose attempted forms include the surface form `w`.
  This is the derived index that fixes the `wound` problem: a label records
  "the readings of *wound* were exactly these", and a new layer invalidates it
  iff it changes that set — including by adding a lemma like `wind`.
* `aux w`      — the slot an auxiliary opens, if `w` is one.
* `reset w`    — whether `w` closes a clause.

## Layers
Newest first. For a lemma, the newest layer that mentions it decides:
retraction, an irregular entry, or a regular listing. So a layer may override
(US `dive/dove` over base `dive`), and a correction is a layer, not an edit.

## Three-valued lexicon
The weak rule applies only to lemmas the lexicon lists as regular. An unknown
verb gets *no* past (`none`), not a guess — that is what makes "absent" an
honest, recordable assumption instead of a default that silently fires.
-/

namespace GrammarStore.English

/-! ## Lexical status -/

inductive Status where
  | irregular (v : Irregular)
  | regular
  | absent
deriving Repr, DecidableEq

def Status.known : Status → Bool
  | .absent => false
  | _       => true

def formFrom (sel : Irregular → String) (b : String) : Status → Option String
  | .irregular v => some (sel v)
  | .regular     => some (weakPast b)
  | .absent      => none

/-! ## The query interface -/

inductive Q where
  | verb     (b : String)
  | readings (w : String)
  | aux      (w : String)
  | reset    (w : String)
deriving Repr, DecidableEq

def Q.A : Q → Type
  | .verb _     => Status
  | .readings _ => List String
  | .aux _      => Option Slot
  | .reset _    => Bool

instance instDecEqA : (q : Q) → DecidableEq q.A
  | .verb _     => inferInstanceAs (DecidableEq Status)
  | .readings _ => inferInstanceAs (DecidableEq (List String))
  | .aux _      => inferInstanceAs (DecidableEq (Option Slot))
  | .reset _    => inferInstanceAs (DecidableEq Bool)

/-! ## Layers and the oracle -/

structure Layer where
  name        : String := ""
  irregulars  : List Irregular := []
  regulars    : List String := []
  retract     : List String := []
  auxiliaries : List (String × Slot) := []
  resets      : List String := []
deriving Repr

def statusIn : List Layer → String → Status
  | [], _ => .absent
  | l :: ls, b =>
    if l.retract.contains b then .absent
    else match l.irregulars.find? (·.base == b) with
      | some v => .irregular v
      | none   => if l.regulars.contains b then .regular else statusIn ls b

def lemmasIn (ls : List Layer) : List String :=
  (ls.flatMap fun l => l.irregulars.map (·.base) ++ l.regulars).eraseDups.filter
    fun b => (statusIn ls b).known

/-- Forms a speaker might produce when aiming at lemma `v`, right or wrong. -/
def attemptsIn (ls : List Layer) (v : String) : List String :=
  let st := statusIn ls v
  [v] ++ (formFrom Irregular.past v st).toList ++ (formFrom Irregular.pp v st).toList
    ++ [weakPast v, v ++ "ed", doubled v]

def readingsIn (ls : List Layer) (w : String) : List String :=
  (lemmasIn ls).filter fun v => (attemptsIn ls v).contains w

def auxIn (ls : List Layer) (w : String) : Option Slot :=
  ls.findSome? fun l => List.lookup w l.auxiliaries

def resetIn (ls : List Layer) (w : String) : Bool :=
  ls.any fun l => l.resets.contains w

def answer (ls : List Layer) : (q : Q) → q.A
  | .verb b     => statusIn ls b
  | .readings w => readingsIn ls w
  | .aux w      => auxIn ls w
  | .reset w    => resetIn ls w

/-! ## Rules -/

inductive Rule where
  | table     (b : String) (v : Irregular)
  | weak      (b : String)
  | auxiliary (w : String) (s : Slot)
  | boundary  (w : String)
  | ambiguous (w : String) (lemmas : List String)
deriving Repr

abbrev G := Prog Q Q.A Rule

def verbQ     (b : String) : G Status        := .ask (.verb b) fun x => .pure x
def readingsQ (w : String) : G (List String) := .ask (.readings w) fun x => .pure x
def auxQ      (w : String) : G (Option Slot) := .ask (.aux w) fun x => .pure x
def resetQ    (w : String) : G Bool          := .ask (.reset w) fun x => .pure x

def explain (b : String) : Status → G Unit
  | .irregular v => Prog.because (.table b v)
  | .regular     => Prog.because (.weak b)
  | .absent      => pure ()

/-- Written with constructors rather than `do`, so its run is easy to reason about. -/
def formOf (sel : Irregular → String) (b : String) : G (Option String) :=
  .ask (.verb b) fun st => match (st : Status) with
    | .irregular v => .note (.table b v) (.pure (some (sel v)))
    | .regular     => .note (.weak b) (.pure (some (weakPast b)))
    | .absent      => .pure none

def diagnose (slot : Slot) (irr : Bool) (v w expected past pp : String) : String :=
  let wanted := match slot with
    | .participle => "participle" | .bare => "bare infinitive" | .finite => "simple past"
  let why :=
    if irr && (w == weakPast v || w == v ++ "ed") then "overregularised"
    else if !irr && w == v ++ "ed" then "spelling rule not applied"
    else if w == doubled v then "consonant wrongly doubled"
    else if w == past then s!"simple past where {wanted} is needed"
    else if w == pp then s!"participle where {wanted} is needed"
    else "wrong form"
  s!"'{w}' → '{expected}' ({why})"

/-- Check one word `w` read as lemma `v`, in a given slot. -/
def checkWord (slot : Slot) (v w : String) : G (Option String) := do
  let st ← verbQ v
  explain v st
  let some past := formFrom Irregular.past v st | pure none
  let some pp   := formFrom Irregular.pp v st   | pure none
  let ok := match slot with
    | .participle => w == pp
    | .bare       => w == v
    | .finite     => w == v || w == past
  if ok then pure none
  else
    let expected := match slot with
      | .participle => pp
      | .bare       => v
      | .finite     => past
    let irr := match st with
      | .irregular _ => true
      | _            => false
    pure (some (diagnose slot irr v w expected past pp))

/-- Left-to-right scan. An auxiliary opens a slot that the next verb fills;
the verb, or a clause boundary, closes it. An ambiguous word is an error only
if *every* reading is wrong. -/
def checkProg (s : String) : G (List String) := do
  let mut slot := Slot.finite
  let mut errs : List String := []
  for w in tokens s do
    match (← auxQ w) with
    | some sl =>
      Prog.because (.auxiliary w sl)
      slot := sl
    | none =>
      if (← resetQ w) then
        Prog.because (.boundary w)
        slot := .finite
      else
        match (← readingsQ w) with
        | [] => pure ()
        | [v] =>
          errs := errs ++ (← checkWord slot v w).toList
          slot := .finite
        | vs =>
          Prog.because (.ambiguous w vs)
          let results ← vs.mapM (checkWord slot · w)
          if results.all Option.isSome then
            errs := errs ++ (results.head?.join.toList.map
              (· ++ s!" [readings: {", ".intercalate vs}]"))
          slot := .finite
  return errs

/-! ## Goals, answers, display -/

inductive Goal where
  | past  (b : String)
  | pp    (b : String)
  | check (s : String)
deriving Repr, DecidableEq

inductive Ans where
  | form   (p : Option String)
  | errors (es : List String)
deriving Repr, DecidableEq

def showGoal : Goal → String
  | .past b  => s!"past {b}"
  | .pp b    => s!"pp {b}"
  | .check s => s!"check \"{s}\""

def showAns : Ans → String
  | .form (some p) => p
  | .form none     => "(no judgment: verb not in lexicon)"
  | .errors []     => "ok"
  | .errors es     => "\n".intercalate es

def showStatus : Status → String
  | .irregular v => s!"irregular {v.past}/{v.pp}"
  | .regular     => "regular"
  | .absent      => "not in lexicon"

def showReadings (w : String) (vs : List String) : String :=
  if vs.isEmpty then s!"'{w}' is not a verb form" else s!"'{w}' reads as {", ".intercalate vs}"

def showAux (w : String) : Option Slot → String
  | some s => s!"'{w}' opens a {showSlot s} slot"
  | none   => s!"'{w}' is not an auxiliary"

def showReset (w : String) (b : Bool) : String :=
  if b then s!"'{w}' closes a clause" else s!"'{w}' does not close a clause"

def showAsked : (q : Q) → q.A → String
  | .verb b, st     => s!"{b} is {showStatus st}"
  | .readings w, vs => showReadings w vs
  | .aux w, a       => showAux w a
  | .reset w, b     => showReset w b

def showRule : Rule → String
  | .table b v       => s!"{b}: table entry {v.base}/{v.past}/{v.pp}"
  | .weak b          => s!"{b}: weak rule"
  | .auxiliary w s   => s!"'{w}' opens a {showSlot s} slot"
  | .boundary w      => s!"'{w}' closes the clause"
  | .ambiguous w vs  => s!"'{w}' is ambiguous: {", ".intercalate vs}"

def showEvent : Event Q Q.A Rule → String
  | .asked q a => showAsked q a
  | .noted r   => showRule r

/-! ## The domain -/

@[reducible] def english : Domain where
  Q := Q
  A := Q.A
  R := Rule
  Layer := Layer
  Goal := Goal
  Ans := Ans
  answer := answer
  prog := fun
    | .past b  => Ans.form <$> formOf Irregular.past b
    | .pp b    => Ans.form <$> formOf Irregular.pp b
    | .check s => Ans.errors <$> checkProg s
  decA := instDecEqA
  decGoal := inferInstance
  showEvent := showEvent
  showAns := showAns

/-! ## Domain theorems — the expertise-specific part -/

theorem run_formOf (o : (q : Q) → q.A) (sel : Irregular → String) (b : String) :
    (formOf sel b).run o = formFrom sel b (o (.verb b)) := by
  unfold formOf
  simp only [Prog.run]
  generalize o (.verb b) = st
  cases st <;> rfl

/-- Weak verbs: past = participle. -/
theorem past_eq_pp_of_regular {o : (q : Q) → q.A} {b : String} (h : o (.verb b) = Status.regular) :
    (formOf Irregular.past b).run o = (formOf Irregular.pp b).run o := by
  simp [run_formOf, h, formFrom]

/-- No lexicon entry, no judgment: the weak rule does not fire on unknown verbs. -/
theorem formOf_absent {o : (q : Q) → q.A} {b : String} (sel : Irregular → String)
    (h : o (.verb b) = Status.absent) : (formOf sel b).run o = none := by
  simp [run_formOf, h, formFrom]

abbrev PastOf (ls : List Layer) (b p : String) : Prop := (formOf Irregular.past b).run (answer ls) = some p
abbrev PPOf   (ls : List Layer) (b p : String) : Prop := (formOf Irregular.pp b).run (answer ls) = some p

/-- One verb, one form — per grammar. -/
theorem PastOf.unique {ls : List Layer} {b p q : String}
    (hp : PastOf ls b p) (hq : PastOf ls b q) : p = q := by
  cases hp.symm.trans hq
  rfl

/-! ## The base grammar and a US branch -/

def baseLayer : Layer where
  name := "base"
  irregulars :=
    [ ⟨"sing",  "sang",    "sung",    .strong⟩
    , ⟨"drink", "drank",   "drunk",   .strong⟩
    , ⟨"swim",  "swam",    "swum",    .strong⟩
    , ⟨"run",   "ran",     "run",     .strong⟩
    , ⟨"write", "wrote",   "written", .strong⟩
    , ⟨"take",  "took",    "taken",   .strong⟩
    , ⟨"eat",   "ate",     "eaten",   .strong⟩
    , ⟨"see",   "saw",     "seen",    .strong⟩
    , ⟨"teach", "taught",  "taught",  .weakIrreg⟩
    , ⟨"bring", "brought", "brought", .weakIrreg⟩
    , ⟨"think", "thought", "thought", .weakIrreg⟩
    , ⟨"put",   "put",     "put",     .weakIrreg⟩
    , ⟨"cut",   "cut",     "cut",     .weakIrreg⟩
    , ⟨"go",    "went",    "gone",    .suppletive⟩ ]
  regulars :=
    [ "walk", "stop", "carry", "play", "bake", "visit", "plan", "want", "box", "kick"
    , "fix", "snow", "learn", "dive", "wound" ]
  auxiliaries :=
    (["have", "has", "had", "having", "be", "is", "are", "was", "were", "been", "being"].map
      (·, Slot.participle)) ++
    (["do", "does", "did"].map (·, Slot.bare))
  resets := ["and", "but", "then", "or", "no", "yes"]

def usLayer : Layer :=
  { name := "us", irregulars := [⟨"dive", "dove", "dived", .strong⟩] }

def windLayer : Layer :=
  { name := "+wind", irregulars := [⟨"wind", "wound", "wound", .strong⟩] }

def base : KB english := ⟨[baseLayer]⟩

-- Kernel-checked judgments, relative to a grammar:
example : PastOf [baseLayer] "teach" "taught"           := by decide +kernel
example : ¬ PastOf [baseLayer] "teach" "teached"        := by decide +kernel
example : PastOf [baseLayer] "stop" "stopped"           := by decide +kernel
example : PPOf [baseLayer] "run" "run"                  := by decide +kernel
example : PastOf [baseLayer] "dive" "dived"             := by decide +kernel
example : PastOf [usLayer, baseLayer] "dive" "dove"     := by decide +kernel
example : (formOf Irregular.past "blorf").run (answer [baseLayer]) = none := by decide +kernel

def demo : IO Unit := do
  let s := Session.init base
  let (e1, s) := s.ask (Goal.check "She dived in and teached us.")
  IO.println e1.render
  let (e2, s) := s.ask (Goal.past "teach")
  IO.println e2.render
  let (e3, s) := s.ask (Goal.check "The wound healed.")
  IO.println e3.render
  let r := s.push usLayer
  IO.println s!"\n+us: kept {r.kept.length}, dropped {r.dropped.map (showGoal ·.goal)}"
  let r := r.session.push windLayer
  IO.println s!"+wind: kept {r.kept.length}, dropped {r.dropped.map (showGoal ·.goal)}"
  let (e4, _) := r.session.ask (Goal.check "She dived in and teached us.")
  IO.println e4.render

#eval demo

end GrammarStore.English
