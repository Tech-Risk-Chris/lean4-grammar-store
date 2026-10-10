/-!
# English morphology: the pure, layer-independent part

Carried over unchanged from `VerbForms.lean`: principal parts, the weak-past
spelling rule, tokenisation. Nothing here consults a knowledge base.
-/

namespace GrammarStore.English

/-- Historical class, kept because "irregular" lumps together three different things. -/
inductive VClass where
  | strong       -- ablaut: sing/sang/sung
  | weakIrreg    -- dental suffix with vowel change or assimilation: teach/taught, put/put
  | suppletive   -- past from a different root: go/went (< wend)
deriving Repr, DecidableEq

structure Irregular where
  base : String
  past : String
  pp   : String
  cls  : VClass
deriving Repr, DecidableEq

def isVowel (c : Char) : Bool := ['a', 'e', 'i', 'o', 'u'].elem c

/-- Number of maximal vowel runs — a crude syllable count. -/
def syllables (cs : List Char) : Nat :=
  (cs.foldl (fun (n, prevV) c =>
      let v := isVowel c
      (if v && !prevV then n + 1 else n, v)) (0, false)).1

/-- Weak past / past participle, orthographically. Doubling really depends on
stress (admit → admitted), which spelling doesn't encode. -/
def weakPast (b : String) : String :=
  let cs := b.toList
  match cs.reverse with
  | 'e' :: _ => b ++ "d"
  | 'y' :: c :: _ =>
      if isVowel c then b ++ "ed" else String.ofList cs.dropLast ++ "ied"
  | c :: v :: p :: _ =>
      if !isVowel c && isVowel v && !isVowel p && !['w', 'x', 'y'].elem c && syllables cs == 1
      then b.push c ++ "ed" else b ++ "ed"
  | _ => b ++ "ed"

/-- `v` with its final letter doubled, then `-ed`: the mistake *boxxed*, *visitted*. -/
def doubled (v : String) : String :=
  match v.toList.getLast? with
  | some c => v.push c ++ "ed"
  | none   => v ++ "ed"

inductive Slot where
  | participle   -- after have/has/had, be/was/were/been
  | bare         -- after do/does/did
  | finite       -- otherwise: base (present) or simple past
deriving Repr, DecidableEq

def showSlot : Slot → String
  | .participle => "participle"
  | .bare       => "bare infinitive"
  | .finite     => "finite"

/-- Split on non-letters and lowercase (over `List Char`, to stay clear of the
`String.split` API change). -/
def tokens (s : String) : List String :=
  let step := fun (c : Char) (acc : List Char × List String) =>
    let (cur, out) := acc
    if c.isAlpha then (c.toLower :: cur, out)
    else if cur.isEmpty then ([], out)
    else ([], String.ofList cur :: out)
  let (cur, out) := s.toList.foldr step ([], [])
  if cur.isEmpty then out else String.ofList cur :: out

end GrammarStore.English
