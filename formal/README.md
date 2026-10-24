# A checker of Kater's certificates, proved sound

When Kater proves an inclusion between two automata, it can hand out a
certificate of the proof (`Checker::Certificate`). This Lean 4 project has a
checker of these certificates and a proof that it is sound: if it accepts a
certificate, and the letter inclusions the certificate rests on hold, the
left automaton's relation is within the right one's.

| File | What it has |
|------|-------------|
| `KaterCert/Rel.lean` | relations on events |
| `KaterCert/Label.lean` | Kater's letters and what they mean |
| `KaterCert/NFA.lean` | automata, and the relations of words and automata |
| `KaterCert/Conditions.lean` | the four conditions of a certificate, and why they suffice |
| `KaterCert/Checker.lean` | `Certificate.check`: `checkCertificate` of `tests/oracle/Certificate.cpp`, in Lean |
| `KaterCert/Soundness.lean` | `check_sound`: the checker is sound |
| `KaterCert/Read.lean`, `Main.lean` | `kater-cert-check`: reads and checks certificates written as JSON |

`lake build` checks the proof and builds `kater-cert-check`. To check the
certificates of Kater's test suite, from the repository's root, with a build
configured with `-DBUILD_TESTS=ON`:

    Release/kater-oracle certify -n 1 --json /tmp/certificates tests/correct/*/*.kat
    cd formal && lake exe kater-cert-check /tmp/certificates

`ctest -L formal` does the same. See `doc/verification.md` (The checker in
Lean) for the model, what the proof needs, and what remains trusted.
