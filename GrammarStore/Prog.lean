/-!
# Programs over a query interface

The one idea everything else rests on: a rule never touches the knowledge base
directly. It is a `Prog`, a program that can only *ask* questions (`ask`) and
*log* which rule it applied (`note`). Running a program against an oracle gives
an answer; tracing it gives the exact questions it asked and the answers it got.

That trace is the ATMS label of the answer. `run_congr` (proved once, for every
domain) says: if another oracle answers every recorded question the same way,
the program computes the same answer there. `trace_congr` says the trace itself
is reproduced, which is what lets a cache entry survive any number of rebases.

Compare *Build Systems à la Carte* (Mokhov, Mitchell, Peyton Jones): monadic
tasks, dynamic dependencies, verifying traces.
[Link](https://simon.peytonjones.org/assets/pdfs/build-systems-jfp.pdf)
-/

namespace GrammarStore

/-- `Q`: questions. `A q`: the type of answers to `q`. `R`: rule names, for explanations. -/
inductive Prog (Q : Type) (A : Q → Type) (R : Type) (α : Type) : Type where
  | pure : α → Prog Q A R α
  | ask  : (q : Q) → (A q → Prog Q A R α) → Prog Q A R α
  | note : R → Prog Q A R α → Prog Q A R α

/-- One step of a trace: a question with the answer it received, or a rule application. -/
inductive Event (Q : Type) (A : Q → Type) (R : Type) : Type where
  | asked : (q : Q) → A q → Event Q A R
  | noted : R → Event Q A R

namespace Event
variable {Q : Type} {A : Q → Type} {R : Type}

/-- An oracle agrees with an event if it gives the recorded answer. Rule notes carry no assumption. -/
def Agrees (o : (q : Q) → A q) : Event Q A R → Prop
  | .asked q a => o q = a
  | .noted _   => True

instance [∀ q, DecidableEq (A q)] (o : (q : Q) → A q) :
    (e : Event Q A R) → Decidable (e.Agrees o)
  | .asked q a => inferInstanceAs (Decidable (o q = a))
  | .noted _   => inferInstanceAs (Decidable True)

def isAsk : Event Q A R → Bool
  | .asked .. => true
  | .noted _  => false

end Event

namespace Prog
variable {Q : Type} {A : Q → Type} {R α β : Type}

def bind : Prog Q A R α → (α → Prog Q A R β) → Prog Q A R β
  | .pure a,   f => f a
  | .ask q k,  f => .ask q (fun x => bind (k x) f)
  | .note r p, f => .note r (bind p f)

instance : Monad (Prog Q A R) where
  pure := Prog.pure
  bind := Prog.bind

def query (q : Q) : Prog Q A R (A q) := .ask q Prog.pure

def because (r : R) : Prog Q A R Unit := .note r (Prog.pure ())

/-- Semantics: answer every question with the oracle; rule notes are invisible. -/
def run (o : (q : Q) → A q) : Prog Q A R α → α
  | .pure a   => a
  | .ask q k  => run o (k (o q))
  | .note _ p => run o p

/-- The questions actually asked, with their answers, interleaved with rule notes. -/
def trace (o : (q : Q) → A q) : Prog Q A R α → List (Event Q A R)
  | .pure _   => []
  | .ask q k  => .asked q (o q) :: trace o (k (o q))
  | .note r p => .noted r :: trace o p

/-- **The** theorem: an answer depends only on the questions it asked. -/
theorem run_congr {o o' : (q : Q) → A q} (p : Prog Q A R α)
    (h : ∀ e ∈ p.trace o, e.Agrees o') : p.run o' = p.run o := by
  induction p with
  | pure _ => rfl
  | ask q k ih =>
    have hq : o' q = o q := h (.asked q (o q)) (by simp [Prog.trace])
    simp only [Prog.run, hq]
    exact ih (o q) (fun e he => h e (by simp [Prog.trace, he]))
  | note r p ih =>
    simp only [Prog.run]
    exact ih (fun e he => h e (by simp [Prog.trace, he]))

/-- …and the trace is reproduced too, so validity is stable under repeated rebasing. -/
theorem trace_congr {o o' : (q : Q) → A q} (p : Prog Q A R α)
    (h : ∀ e ∈ p.trace o, e.Agrees o') : p.trace o' = p.trace o := by
  induction p with
  | pure _ => rfl
  | ask q k ih =>
    have hq : o' q = o q := h (.asked q (o q)) (by simp [Prog.trace])
    simp only [Prog.trace, hq, ih (o q) (fun e he => h e (by simp [Prog.trace, he]))]
  | note r p ih =>
    simp only [Prog.trace, ih (fun e he => h e (by simp [Prog.trace, he]))]

end Prog
end GrammarStore
