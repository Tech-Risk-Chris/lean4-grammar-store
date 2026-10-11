import GrammarStore.Prog

/-!
# The store: domains, layered knowledge bases, a self-validating cache

Nothing in this file knows about grammar. A `Domain` packages
* a query interface (`Q`, `A`) and rule names (`R`),
* a layer type and an `answer` function: how a stack of layers answers a query
  (override, retraction, derived indexes are all the domain's business),
* goals and the `Prog` that answers each one.

A `Session` is a knowledge base plus a cache of answered goals. Each cached
`Entry` keeps its trace. Moving the session to *any* other knowledge base
(push a layer, pop one, switch branch) is `rebase`: keep the entries whose
trace the new knowledge base still agrees with, drop the rest.

Invariant (`Coherent`): every cached entry is exactly what recomputing it
against the current knowledge base would produce. `init`, `ask` and `rebase`
preserve it, so `ask_correct` holds: a cache hit is never stale.
-/

namespace GrammarStore

structure Domain where
  Q         : Type
  A         : Q → Type
  R         : Type
  Layer     : Type
  Goal      : Type
  Ans       : Type
  /-- How a stack of layers (newest first) answers each question. -/
  answer    : List Layer → (q : Q) → A q
  /-- The rule program for each goal. -/
  prog      : Goal → Prog Q A R Ans
  decA      : ∀ q, DecidableEq (A q)
  decGoal   : DecidableEq Goal
  showEvent : Event Q A R → String
  showAns   : Ans → String

instance instDecA {D : Domain} (q : D.Q) : DecidableEq (D.A q) := D.decA q
instance instDecGoal {D : Domain} : DecidableEq D.Goal := D.decGoal

/-! ## Knowledge bases -/

structure KB (D : Domain) where
  /-- Newest layer first. -/
  layers : List D.Layer

namespace KB
variable {D : Domain}
def oracle (kb : KB D) : (q : D.Q) → D.A q := D.answer kb.layers
def push (kb : KB D) (l : D.Layer) : KB D := ⟨l :: kb.layers⟩
def pop  (kb : KB D) : KB D := ⟨kb.layers.tail⟩
end KB

/-! ## Cache entries -/

structure Entry (D : Domain) where
  goal  : D.Goal
  ans   : D.Ans
  trace : List (Event D.Q D.A D.R)

namespace Entry
variable {D : Domain}

/-- Answer a goal from scratch, keeping the trace. -/
def record (kb : KB D) (g : D.Goal) : Entry D :=
  { goal := g, ans := (D.prog g).run kb.oracle, trace := (D.prog g).trace kb.oracle }

/-- What it means for an entry to be right about a knowledge base. -/
def Holds (kb : KB D) (e : Entry D) : Prop := e.ans = (D.prog e.goal).run kb.oracle

/-- Does `kb` give every recorded answer? Decidable, and cheap relative to recomputation
only when the answers are expensive; its real point is that it says *which* assumption broke. -/
def agrees (e : Entry D) (kb : KB D) : Bool :=
  e.trace.all fun ev => decide (ev.Agrees kb.oracle)

/-- The questions this answer depends on: its label. -/
def label (e : Entry D) : List (Event D.Q D.A D.R) := e.trace.filter (·.isAsk)

/-- The rules it applied: its explanation. -/
def rules (e : Entry D) : List (Event D.Q D.A D.R) := e.trace.filter (fun ev => !ev.isAsk)

def render (e : Entry D) : String :=
  let because  := (e.rules.map D.showEvent).eraseDups
  let assuming := (e.label.map D.showEvent).eraseDups
  let sec (name : String) (xs : List String) : String :=
    if xs.isEmpty then "" else s!"\n  {name}{"; ".intercalate xs}"
  D.showAns e.ans ++ sec "because:  " because ++ sec "assuming: " assuming

theorem record_holds (kb : KB D) (g : D.Goal) : (record kb g).Holds kb := rfl

/-- An entry that agrees with `kb'` *is* the entry `kb'` would record. -/
theorem record_eq {kb kb' : KB D} {g : D.Goal} (h : (record kb g).agrees kb' = true) :
    record kb' g = record kb g := by
  have hall : ∀ e ∈ (D.prog g).trace kb.oracle, e.Agrees kb'.oracle :=
    fun e he => of_decide_eq_true (List.all_eq_true.mp h e he)
  simp only [record, Prog.run_congr _ hall, Prog.trace_congr _ hall]

theorem stable {kb kb' : KB D} {e : Entry D} (he : e = record kb e.goal)
    (h : e.agrees kb' = true) : e = record kb' e.goal := by
  have h' : (record kb e.goal).agrees kb' = true := by rw [← he]; exact h
  rw [record_eq h']
  exact he

end Entry

/-! ## Sessions -/

structure Session (D : Domain) where
  kb    : KB D
  cache : List (Entry D)

structure Rebased (D : Domain) where
  session : Session D
  kept    : List (Entry D)
  dropped : List (Entry D)

namespace Session
variable {D : Domain}

def init (kb : KB D) : Session D := ⟨kb, []⟩

def Coherent (s : Session D) : Prop := ∀ e ∈ s.cache, e = Entry.record s.kb e.goal

def lookup (s : Session D) (g : D.Goal) : Option (Entry D) := s.cache.find? (·.goal == g)

def ask (s : Session D) (g : D.Goal) : Entry D × Session D :=
  match s.lookup g with
  | some e => (e, s)
  | none   => (Entry.record s.kb g, { s with cache := Entry.record s.kb g :: s.cache })

/-- Move to any knowledge base; keep exactly the entries whose labels still hold. -/
def rebase (s : Session D) (kb' : KB D) : Rebased D :=
  { session := { kb := kb', cache := s.cache.filter (·.agrees kb') }
    kept    := s.cache.filter (·.agrees kb')
    dropped := s.cache.filter (fun e => !e.agrees kb') }

def push (s : Session D) (l : D.Layer) : Rebased D := s.rebase (s.kb.push l)
def pop  (s : Session D) : Rebased D := s.rebase s.kb.pop

theorem init_coherent (kb : KB D) : (init kb).Coherent := by
  unfold Coherent
  intro e he
  simp [init] at he

theorem ask_coherent {s : Session D} (hs : s.Coherent) (g : D.Goal) : (s.ask g).2.Coherent := by
  unfold ask
  split
  · exact hs
  · unfold Coherent at hs ⊢
    intro e he
    simp only [List.mem_cons] at he
    rcases he with rfl | he
    · rfl
    · exact hs e he

/-- A cache hit is never stale. -/
theorem ask_correct {s : Session D} (hs : s.Coherent) (g : D.Goal) :
    (s.ask g).1 = Entry.record s.kb g := by
  unfold ask
  split
  next e hfind =>
    unfold lookup at hfind
    have hg : e.goal = g := by simpa using List.find?_some hfind
    have hmem := List.mem_of_find?_eq_some hfind
    show e = _
    rw [hs e hmem, hg]
  next => rfl

theorem ask_holds {s : Session D} (hs : s.Coherent) (g : D.Goal) : (s.ask g).1.Holds s.kb := by
  rw [ask_correct hs g]
  exact Entry.record_holds _ _

theorem rebase_coherent {s : Session D} (hs : s.Coherent) (kb' : KB D) :
    (s.rebase kb').session.Coherent := by
  unfold Coherent at hs ⊢
  intro e he
  simp only [rebase, List.mem_filter] at he
  exact Entry.stable (hs e he.1) he.2

theorem push_coherent {s : Session D} (hs : s.Coherent) (l : D.Layer) :
    (s.push l).session.Coherent := rebase_coherent hs _

theorem pop_coherent {s : Session D} (hs : s.Coherent) : s.pop.session.Coherent :=
  rebase_coherent hs _

end Session
end GrammarStore
