import KaterCert.EndToEnd

/-!
`kater-chain-check [-v] PATH...`: checks the evidence of whole proofs in PATH
(files, or directories of `.json` files) as `kater-oracle evidence --json`
writes it (`EndToEnd.check`), printing why it rejects each assertion it
rejects, and with `-v` the time each takes. Exits with 1 if a file does not
read or an assertion is rejected. `--profile FILE` and `--profile-step FILE
K` time the searches of the checks, for triage.
-/

open KaterCert

def files (paths : List String) : IO (Array System.FilePath) := do
  let mut result := #[]
  for p in paths do
    let path : System.FilePath := p
    if ← path.isDir then
      for e in ← path.readDir do
        if e.path.extension == some "json" then
          result := result.push e.path
    else
      result := result.push path
  return result.qsort fun a b => a.toString < b.toString

/-- A word of `X` that the certificate's configurations do not match, for
triage: the letters to the first configuration that fails, and why. -/
def explain (θ : Theory) (X Y : NFA Label) (cycle : Bool) (limit : Nat)
    (hint : Option (Array (List Nat)) := none) : IO Unit := do
  match Guarded.search θ X Y cycle limit hint with
  | none => IO.println "  search gave up"
  | some c =>
    -- parents: for each macro, the macro and letter it was first reached by
    let mut parent : Array (Option (Nat × Label)) := Array.replicate c.macros.size none
    for i in [0:c.macros.size] do
      let m := c.macros[i]!
      let idx := c.succ[i]!
      -- the letters of the steps, in order: recompute which transitions produced steps
      let labs := (X.trans m.x).filter fun t =>
        (match t.1.rel with
         | none => !θ.unsat (Guarded.union m.tests t.1.pre)
         | some r => !(θ.unsat (Guarded.union (Guarded.union m.tests t.1.pre) (θ.dom r)) ||
             θ.unsat (Guarded.union t.1.post (θ.codom r))))
      for (j, t) in idx.zip labs do
        if j != i && parent[j]!.isNone then parent := parent.set! j (some (i, t.1))
    let word (i : Nat) : List String := Id.run do
      let mut out := []
      let mut k := i
      for _ in [0:c.macros.size] do
        match parent[k]! with
        | some (j, l) => out := (repr l).pretty :: out; k := j
        | none => break
      return out
    for i in [0:c.macros.size] do
      let m := c.macros[i]!
      if !Guarded.acceptOk θ X Y cycle m then
        IO.println s!"  X accepts at {m.x} with tests {repr m.tests}, Y does not; right {repr m.right}"
        IO.println s!"  word: {word i}"
        match hint with
        | some h =>
          IO.println s!"  origins of {m.x}: {h.getD m.x []}"
          -- the configurations along the word
          let mut k := i
          for _ in [0:c.macros.size] do
            let mk := c.macros[k]!
            IO.println s!"    at {mk.x} (origins {h.getD mk.x []}): right {repr (mk.right.map (·.1))}"
            match parent[k]! with
            | some (j, _) => k := j
            | none => break
        | none => pure ()
        return
    IO.println "  every configuration accepts where X does"

def timeIt (name : String) (θ : Theory) (X Y : NFA Label) (cycle : Bool) (limit : Nat)
    (hint : Option (Array (List Nat)) := none) : IO Unit := do
  if hint.isSome then
    let s0 ← IO.monoMsNow
    let rs := Guarded.search θ X Y cycle limit hint
    let ns := match rs with | some c => c.macros.size | none => 0
    let s1 ← IO.monoMsNow
    let oks := match rs with | some c => Guarded.check θ X Y cycle c | none => false
    let s2 ← IO.monoMsNow
    IO.println s!"{name} (hinted): macros {ns} search {s1-s0} ms check {s2-s1} ms ok {oks}"
    if !oks && X.size < 1100 then explain θ X Y cycle limit hint
  let t0 ← IO.monoMsNow
  let r := Guarded.search θ X Y cycle limit
  let n := match r with | some c => c.macros.size | none => 0
  let t1 ← IO.monoMsNow
  let ok := match r with | some c => Guarded.check θ X Y cycle c | none => false
  let t2 ← IO.monoMsNow
  IO.println s!"{name}: X {X.size} Y {Y.size} macros {n} search {t1-t0} ms check {t2-t1} ms ok {ok}"
  if n == 0 then
    -- statistics of a search that gave up, at a smaller limit
    match Guarded.search θ X Y cycle (limit / 4) with
    | some _ => pure ()
    | none =>
      let r := Guarded.statsSearch θ X Y cycle (limit / 4)
      IO.println s!"  gave up: {r}"

def profile (f : System.FilePath) (limit : Nat) : IO Unit := do
  match ReadChain.evidence (← IO.FS.readFile f) with
  | .error e => IO.println e
  | .ok ev =>
    let θ := Theory.ofDecls (Whole.declsOf ev)
    for inc in ev.inclusions do
      let lhs := Exp.expandRfs inc.lhs inc.rhs
      let L := (inc.steps.find? (·.stage == "leftFinal")).get!.nfa
      timeIt "left" θ (Thompson.nfa lhs) L false limit
      if !Guarded.prove θ (Thompson.nfa lhs) L false then explain θ (Thompson.nfa lhs) L false limit
      timeIt "right" θ inc.chain.start (Thompson.nfa inc.rhs) false limit
      let mut prev := inc.chain.start
      for (p, o) in Whole.withOrigins inc.chain.passes inc.chainOrigins.tail do
        if p.name == "normalize" || p.name == "prune" then
          timeIt p.name θ p.result prev false limit (some o)
        prev := p.result

/-- Profiles pass `k` of the first inclusion's right side against the
automaton before it. -/
def profileStep (f : System.FilePath) (k limit : Nat) : IO Unit := do
  match ReadChain.evidence (← IO.FS.readFile f) with
  | .error e => IO.println e
  | .ok ev =>
    let θ := Theory.ofDecls (Whole.declsOf ev)
    match ev.inclusions with
    | inc :: _ =>
      let ps := Whole.withOrigins inc.chain.passes inc.chainOrigins.tail
      let prev := if k = 0 then some inc.chain.start else (ps[k - 1]?.map (·.1.result))
      match ps[k]?, prev with
      | some (p, o), some prev => timeIt p.name θ p.result prev false limit (some o)
      | _, _ => IO.println "no such pass"
    | [] => IO.println "no inclusion"

def main (args : List String) : IO UInt32 := do
  if args.head? == some "--profile-step" then
    profileStep (args.getD 1 "") (args.getD 2 "1").toNat! (args.getD 3 "20000").toNat!
    return 0
  if args.head? == some "--profile" then
    profile (args.getD 1 "") (args.getD 2 "20000").toNat!
    return 0
  let verbose := args.contains "-v"
  let paths := args.filter (· != "-v")
  if paths.isEmpty then
    IO.eprintln "usage: kater-chain-check [-v] PATH..."
    return 2
  let mut accepted := 0
  let mut rejected := 0
  let mut unread := 0
  for f in ← files paths do
    match ReadChain.evidence (← IO.FS.readFile f) with
    | .error e =>
      IO.println s!"{f}: cannot read: {e}"
      unread := unread + 1
    | .ok ev =>
      let t0 ← IO.monoMsNow
      let r := EndToEnd.check ev
      let t1 ← IO.monoMsNow
      match r with
      | .ok () =>
        accepted := accepted + 1
        if verbose then IO.println s!"{f}: accepted ({t1 - t0} ms): {ev.assertion}"
      | .error why =>
        rejected := rejected + 1
        IO.println s!"{f}: rejected ({t1 - t0} ms): {why}"
  IO.println s!"{accepted} assertions accepted, {rejected} rejected, {unread} unread"
  return if rejected + unread = 0 then 0 else 1
