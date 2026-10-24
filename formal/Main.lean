import KaterCert

/-!
`kater-cert-check [-v] PATH...`: checks the certificates in PATH (files, or
directories of `.json` files) as `kater-oracle certify --json` writes them,
and compares each verdict with the one the file records (`checkCertificate`'s),
or with "valid" if it records none. Exits with 1 if a file does not read or a
verdict differs.
-/

open KaterCert

def verdict : Option String → String
  | none => "valid"
  | some why => s!"invalid: {why}"

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

structure Tally where
  valid : Nat := 0
  invalid : Nat := 0

def Tally.add (t : Tally) (ok : Bool) : Tally :=
  if ok then { t with valid := t.valid + 1 } else { t with invalid := t.invalid + 1 }

def main (args : List String) : IO UInt32 := do
  let verbose := args.contains "-v"
  let paths := args.filter (· != "-v")
  if paths.isEmpty then
    IO.eprintln "usage: kater-cert-check [-v] PATH..."
    return 2
  let mut certificates : Tally := {}
  let mut mutants : Tally := {}
  let mut recorded := 0
  let mut failures := 0
  for f in ← files paths do
    match Read.entry (← IO.FS.readFile f) with
    | .error e =>
      IO.println s!"{f}: cannot read: {e}"
      failures := failures + 1
    | .ok e =>
      let why := e.cert.check
      if e.mutation.isSome then
        mutants := mutants.add why.isNone
      else
        certificates := certificates.add why.isNone
      let expected := e.verdict.getD "valid"
      let differs := expected != verdict why
      if e.verdict.isSome then recorded := recorded + 1
      if differs then failures := failures + 1
      if verbose || differs || (e.mutation.isNone && why.isSome) then
        IO.println s!"{f}: {verdict why}"
      if differs then
        IO.println s!"  expected {expected}: {e.constraint}"
  IO.println s!"{certificates.valid + certificates.invalid} certificates: {certificates.valid} valid, {certificates.invalid} invalid"
  IO.println s!"{mutants.valid + mutants.invalid} mutants: {mutants.valid} valid, {mutants.invalid} invalid"
  IO.println s!"{recorded} recorded verdicts, {failures} files unread or differing"
  return if failures = 0 then 0 else 1
