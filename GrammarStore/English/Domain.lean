import GrammarStore.Store
import GrammarStore.English.Morphology

/-!
# English past tense as a grammar-store domain

## Scope
The checker's expertise is the simple past and the present perfect. Its
standing assumption: every input contains at least one verb form of that
kind. If it finds none, the answer is *out of scope*, not *ok*.

## Queries
Every question a rule may ask is keyed, so a cached answer's label names
exactly what it relied on. Questions sharing a key are merged (that costs no
locality); questions with different keys stay apart.

* `verb b`     — keyed by lemma: irregular entry, regular, or absent.
* `classify w` — keyed by surface form: the word's closed-class memberships
  (pronoun, noun, copula, auxiliary, …) from the layers, plus its verb
  readings (lemmas whose attempted forms include `w` — the derived index
  that fixes the `wound` problem).

## Layers
Newest first. For a lemma, the newest layer that mentions it decides
(retraction, irregular entry, regular listing). For a word's classes, the
newest layer that lists the word decides. Overrides and corrections are
layers, not edits.

## Three-valued lexicon
The weak rule applies only to lemmas the lexicon lists as regular. An unknown
verb gets *no* past (`none`), not a guess.
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

/-! ## Word classes -/

/-- The form of a verb token. Tense is a feature of the form, not a word class:
*was* and *is* are both copulae; *been* and *being* are not finite at all. -/
inductive VForm where
  | infinitive | present | past | participle | gerund
deriving Repr, DecidableEq

/-- A closed-class membership. A word may have several (*had* is past and participle). -/
inductive WordClass where
  | aux (s : Slot) (f : VForm)     -- have/has/had/having, do/does/did
  | copula (f : VForm)             -- be/am/is/are/was/were/been/being; open a participle slot
  | conj                           -- closes a clause
  | pronoun
  | determiner
  | preposition
  | adverb
  | noun
deriving Repr, DecidableEq

structure Analysis where
  classes  : List WordClass
  readings : List String
deriving Repr, DecidableEq

/-! ## The query interface -/

inductive Q where
  | verb     (b : String)
  | classify (w : String)
deriving Repr, DecidableEq

def Q.A : Q → Type
  | .verb _     => Status
  | .classify _ => Analysis

instance instDecEqA : (q : Q) → DecidableEq q.A
  | .verb _     => inferInstanceAs (DecidableEq Status)
  | .classify _ => inferInstanceAs (DecidableEq Analysis)

/-! ## Layers and the oracle -/

structure Layer where
  name       : String := ""
  irregulars : List Irregular := []
  regulars   : List String := []
  retract    : List String := []
  words      : List (String × List WordClass) := []
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

def classesIn (ls : List Layer) (w : String) : List WordClass :=
  (ls.findSome? fun l => List.lookup w l.words).getD []

def answer (ls : List Layer) : (q : Q) → q.A
  | .verb b     => statusIn ls b
  | .classify w => ⟨classesIn ls w, readingsIn ls w⟩

/-! ## Rules -/

inductive Rule where
  | table     (b : String) (v : Irregular)
  | weak      (b : String)
  | auxiliary (w : String) (s : Slot)
  | boundary  (w : String)
  | ambiguous (w : String) (lemmas : List String)
deriving Repr

abbrev G := Prog Q Q.A Rule

def verbQ     (b : String) : G Status   := .ask (.verb b) fun x => .pure x
def classifyQ (w : String) : G Analysis := .ask (.classify w) fun x => .pure x

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

/-! ## Goals and answers -/

inductive Goal where
  | past  (b : String)
  | pp    (b : String)
  | check (s : String)
deriving Repr, DecidableEq

inductive Ans where
  | form       (p : Option String)
  | checked    (errors unknown : List String)
  | outOfScope (unknown : List String)
deriving Repr, DecidableEq

/-- The slot an auxiliary or copula opens, and all the forms the token can be. -/
def auxOf (cs : List WordClass) : Option (Slot × List VForm) :=
  let forms := cs.filterMap fun
    | .aux _ f  => some f
    | .copula f => some f
    | _         => none
  let slot := cs.findSome? fun
    | .aux s _  => some s
    | .copula _ => some Slot.participle
    | _         => none
  slot.map (·, forms)

/-- Left-to-right scan. An auxiliary opens a slot that the next verb fills
(so inversion works: "did you went"); the verb, or a conjunction, closes it.

A verb form *counts toward scope* if it fills an auxiliary's slot or is not
the bare base form, i.e. it is past-shaped, right or wrong. That includes a
participle auxiliary or copula filling a slot ("have been", "has had"). A past
auxiliary left without a verb ("I had the book", "she was happy") counts as well.

An ambiguous word is an error only if every verb reading is wrong and it has
no noun reading. -/
def checkProg (s : String) : G Ans := do
  let mut slot := Slot.finite
  let mut pending : Option Bool := none     -- an open auxiliary slot; `true` if the auxiliary is past
  let mut errs : List String := []
  let mut unknown : List String := []
  let mut sawVerb := false
  for w in tokens s do
    let a ← classifyQ w
    match auxOf a.classes with
    | some (sl, fs) =>
      Prog.because (.auxiliary w sl)
      if pending == some true then sawVerb := true                     -- past aux left verbless
      if pending.isSome && fs.contains .participle then sawVerb := true -- "have been", "has had"
      slot := sl
      pending := some (fs.contains .past)
    | none =>
      if a.classes.contains .conj then
        Prog.because (.boundary w)
        if pending == some true then sawVerb := true
        slot := .finite
        pending := none
      else
        match a.readings with
        | [] =>
          if a.classes.isEmpty then unknown := unknown ++ [w]
        | vs =>
          if vs.length > 1 then Prog.because (.ambiguous w vs)
          let results ← vs.mapM (checkWord slot · w)
          if results.all Option.isSome && !a.classes.contains .noun then
            errs := errs ++ (results.head?.join.toList.map fun e =>
              if vs.length > 1 then e ++ s!" [readings: {", ".intercalate vs}]" else e)
          if vs.any (fun v => slot != .finite || w != v) then sawVerb := true
          slot := .finite
          pending := none
  if pending == some true then sawVerb := true
  if sawVerb then return .checked errs unknown
  else return .outOfScope unknown

/-! ## Display -/

def showGoal : Goal → String
  | .past b  => s!"past {b}"
  | .pp b    => s!"pp {b}"
  | .check s => s!"check \"{s}\""

def endsInEd (w : String) : Bool := w.toList.reverse.take 2 == ['d', 'e']

def showAns : Ans → String
  | .form (some p) => p
  | .form none     => "(no judgment: verb not in lexicon)"
  | .checked es us =>
    let body := if es.isEmpty then ["ok"] else es
    let unchecked := if us.isEmpty then [] else [s!"unchecked: {", ".intercalate us}"]
    "\n".intercalate (body ++ unchecked)
  | .outOfScope us =>
    let hints := (us.filter endsInEd).map fun w =>
      s!"'{w}' looks like the past of a verb not in the lexicon"
    let unk := if us.isEmpty then [] else [s!"unknown: {", ".intercalate us}"]
    "\n".intercalate (["not my expertise: no past or present-perfect verb form found"] ++ hints ++ unk)

def showVForm : VForm → String
  | .infinitive => "infinitive"
  | .present    => "present"
  | .past       => "past"
  | .participle => "participle"
  | .gerund     => "gerund"

def showClass : WordClass → String
  | .aux s f     => s!"{showVForm f} auxiliary ({showSlot s})"
  | .copula f    => s!"{showVForm f} copula"
  | .conj        => "conjunction"
  | .pronoun     => "pronoun"
  | .determiner  => "determiner"
  | .preposition => "preposition"
  | .adverb      => "adverb"
  | .noun        => "noun"

def showStatus : Status → String
  | .irregular v => s!"irregular {v.past}/{v.pp}"
  | .regular     => "regular"
  | .absent      => "not in lexicon"

def showAnalysis (w : String) (a : Analysis) : String :=
  let parts := a.classes.map showClass ++
    (if a.readings.isEmpty then [] else [s!"form of {"/".intercalate a.readings}"])
  s!"'{w}': " ++ (if parts.isEmpty then "unknown" else ", ".intercalate parts)

def showAsked : (q : Q) → q.A → String
  | .verb b, st     => s!"{b}: " ++ showStatus st
  | .classify w, a  => showAnalysis w a

def showRule : Rule → String
  | .table b v      => s!"{b}: table entry {v.base}/{v.past}/{v.pp}"
  | .weak b         => s!"{b}: weak rule"
  | .auxiliary w s  => s!"'{w}' opens a {showSlot s} slot"
  | .boundary w     => s!"'{w}' closes the clause"
  | .ambiguous w vs => s!"'{w}' is ambiguous: {", ".intercalate vs}"

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
    | .check s => checkProg s
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

/-! ## The base grammar and some layers to push -/

def tagAll (c : WordClass) (ws : List String) : List (String × List WordClass) :=
  ws.map (·, [c])

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
  words :=
    [ ("have",   [.aux .participle .infinitive, .aux .participle .present])
    , ("has",    [.aux .participle .present])
    , ("had",    [.aux .participle .past, .aux .participle .participle])
    , ("having", [.aux .participle .gerund])
    , ("be",     [.copula .infinitive])
    , ("am",     [.copula .present])
    , ("is",     [.copula .present])
    , ("are",    [.copula .present])
    , ("was",    [.copula .past])
    , ("were",   [.copula .past])
    , ("been",   [.copula .participle])
    , ("being",  [.copula .gerund])
    , ("do",     [.aux .bare .infinitive, .aux .bare .present])
    , ("does",   [.aux .bare .present])
    , ("did",    [.aux .bare .past]) ] ++
    tagAll .conj ["and", "but", "then", "or", "no", "yes"] ++
    tagAll .pronoun
      ["i", "you", "he", "she", "it", "we", "they", "me", "him", "her", "us", "them",
       "nothing", "something", "everything", "who", "what"] ++
    tagAll .determiner
      ["the", "a", "an", "this", "that", "these", "those", "my", "your", "his", "its", "our",
       "their", "all", "three"] ++
    tagAll .preposition ["in", "on", "at", "to", "from", "with", "by", "into", "of", "for"] ++
    tagAll .adverb
      ["yesterday", "away", "home", "loudly", "seriously", "first", "already", "never", "not"] ++
    tagAll .noun
      ["book", "letter", "student", "apples", "class", "wine", "choir", "bags", "times", "pool",
       "clock"]

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

-- Scope, kernel-checked: the present perfect of *be* is in scope, the present is not.
example : (checkProg "I have been there.").run (answer [baseLayer]) = .checked [] ["there"] := by
  decide +kernel
example : (checkProg "She is happy.").run (answer [baseLayer]) = .outOfScope ["happy"] := by
  decide +kernel

def demo : IO Unit := do
  let mut s := Session.init base
  for sentence in
      [ "She teached us and we have learned nothing."
      , "I have ran three times and he has put it away."
      , "They sung loudly, then the choir had drank all the wine."
      , "We stoped, carryed the bags, and played."
      , "Did you went? No, I did go yesterday and taught the class."
      , "I had the book and ran home; have you seen it?"
      , "The letter was wrote by a student who bringed apples."
      , "They fighted seriously."
      , "They walk home."
      , "She was happy."
      , "She is happy."
      , "I have been there."
      , "The book has been writed."
      , "We have had enough." ] do
    let (e, s') := s.ask (Goal.check sentence)
    s := s'
    IO.println s!"» {sentence}\n{e.render}\n"
  let r := s.push usLayer
  IO.println s!"+us: kept {r.kept.length}, dropped {r.dropped.map (showGoal ·.goal)}"

#eval demo

end GrammarStore.English
