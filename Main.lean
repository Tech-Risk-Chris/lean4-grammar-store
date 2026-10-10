import GrammarStore

/-!
# grammar-store: a line-protocol server

One command per line on stdin; each response ends with a line containing `.`
alone. `serve.py` puts HTTP in front of it.

    past <verb>            pp <verb>            check <sentence>
    irregular <base> <past> <pp> <strong|weakIrreg|suppletive>
    regular <verb>         retract <verb>
    aux <word> <participle|bare>                reset <word>
    pop                    layers               cache
    fork <name>            switch <name>
-/

open GrammarStore GrammarStore.English

def words (s : String) : List String :=
  let step := fun (c : Char) (acc : List Char × List String) =>
    let (cur, out) := acc
    if c.isWhitespace then
      if cur.isEmpty then ([], out) else ([], String.ofList cur :: out)
    else (c :: cur, out)
  let (cur, out) := s.toList.foldr step ([], [])
  if cur.isEmpty then out else String.ofList cur :: out

def parseClass : String → Option VClass
  | "strong"     => some .strong
  | "weakIrreg"  => some .weakIrreg
  | "suppletive" => some .suppletive
  | _            => none

def parseSlot : String → Option Slot
  | "participle" => some .participle
  | "bare"       => some .bare
  | _            => none

structure State where
  name     : String
  cur      : Session english
  branches : List (String × Session english)

def help : String :=
  "commands: past V | pp V | check SENTENCE | irregular B P PP CLASS | regular V | retract V\n" ++
  "          aux W participle|bare | reset W | pop | layers | cache | fork NAME | switch NAME"

def report (r : Rebased english) : String :=
  let dropped := r.dropped.map (fun e => "  - " ++ showGoal e.goal)
  s!"kept {r.kept.length} cached answer(s), dropped {r.dropped.length}" ++
    (if dropped.isEmpty then "" else ":\n" ++ "\n".intercalate dropped)

def askGoal (st : State) (g : Goal) : String × State :=
  let hit := (st.cur.lookup g).isSome
  let (e, s) := st.cur.ask g
  ((if hit then "[cached] " else "") ++ e.render, { st with cur := s })

def pushLayer (st : State) (l : Layer) : String × State :=
  let r := st.cur.push l
  (report r, { st with cur := r.session })

def orEmpty (xs : List String) : String :=
  if xs.isEmpty then "(empty)" else "\n".intercalate xs

def handle (st : State) (line : String) : String × State :=
  match words line with
  | ["past", b] => askGoal st (.past b)
  | ["pp", b]   => askGoal st (.pp b)
  | "check" :: ws => askGoal st (.check (" ".intercalate ws))
  | ["irregular", b, p, pp, c] =>
    match parseClass c with
    | some cls => pushLayer st { name := s!"+irregular {b}", irregulars := [⟨b, p, pp, cls⟩] }
    | none     => ("class must be strong, weakIrreg or suppletive", st)
  | ["regular", b] => pushLayer st { name := s!"+regular {b}", regulars := [b] }
  | ["retract", b] => pushLayer st { name := s!"-{b}", retract := [b] }
  | ["reset", w]   => pushLayer st { name := s!"+reset {w}", resets := [w] }
  | ["aux", w, sl] =>
    match parseSlot sl with
    | some s => pushLayer st { name := s!"+aux {w}", auxiliaries := [(w, s)] }
    | none   => ("slot must be participle or bare", st)
  | ["pop"] =>
    if st.cur.kb.layers.length ≤ 1 then ("refusing to pop the base layer", st)
    else
      let r := st.cur.pop
      (report r, { st with cur := r.session })
  | ["layers"] => (orEmpty (st.cur.kb.layers.map (fun (l : Layer) => l.name)), st)
  | ["cache"]  => (orEmpty (st.cur.cache.map (fun e => showGoal e.goal)), st)
  | ["fork", n] =>
    (s!"forked '{n}' from '{st.name}'", { st with branches := (n, st.cur) :: st.branches })
  | ["switch", n] =>
    match List.lookup n st.branches with
    | none   => (s!"no branch '{n}'", st)
    | some b =>
      -- carry over whatever the current cache knows that is still valid there
      let r := st.cur.rebase b.kb
      let others := st.branches.filter (·.1 != n)
      (s!"switched to '{n}'; " ++ report r,
       { name := n
         cur := { kb := b.kb, cache := r.kept ++ b.cache }
         branches := (st.name, st.cur) :: others })
  | _ => (help, st)

partial def loop (st : State) : IO Unit := do
  let line ← (← IO.getStdin).getLine
  if line.isEmpty then return            -- EOF
  let (out, st') := handle st line
  IO.println out
  IO.println "."
  (← IO.getStdout).flush
  loop st'

def main : IO Unit :=
  loop { name := "base", cur := Session.init base, branches := [] }
