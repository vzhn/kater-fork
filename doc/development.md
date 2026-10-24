# Building Kater

Kater needs a C++23 compiler (e.g., GCC >= 14), CMake, flex (>= 2.6) and bison
(>= 3.2). On a Debian-based system:

```shell
apt-get install cmake make g++ flex bison libfl-dev
```

For a release build:

```shell
cmake -DCMAKE_BUILD_TYPE=Release -B Release -S .
cmake --build Release -j$(nproc)
```

This leaves the `kater` executable in `Release/`.

## Build options

 - `KATER_DEBUG`: enable Kater's debugging infrastructure (the `KATER_DEBUG`/
   `DEBUG_WITH_TYPE` logging macros). Enabled by default for `Debug` builds, off
   otherwise.
 - `TIDY`: run `clang-tidy` as part of the build (wires `CMAKE_CXX_CLANG_TIDY`
   with the repo's `.clang-tidy`).

A `compile_commands.json` is always emitted (see *Editor setup* below).

# Testing Kater

## Running tests

Run the test suite (the `tests/correct` and `tests/wrong` cases):

```shell
cd scripts && ./checkall.sh
```

Environment variables affecting the testing scripts:

```shell
  KATER="path/to/kater"          # kater executable to test (default: Release/kater)
  KATERFLAGS="--flag --another"  # extra flags passed to every kater invocation
```

With Z3 installed, a build configured with `-DBUILD_TESTS=ON` also has
`kater-oracle`, which checks Kater's verdicts, its builtin theory, its
automaton passes and its exports against a reference semantics of execution
graphs. Its tests are labeled `oracle`:

```shell
cd Release && ctest -L oracle
```

Given a GenMC source tree, the build also runs the exported GenMC checkers on
small graphs against that semantics (it builds GenMC's core library, without
LLVM, in the build directory); those tests are labeled `genmc`:

```shell
cmake -DGENMC_SOURCE_DIR=path/to/genmc Release
cd Release && ctest -L genmc
```

`formal/` is a Lean 4 project that proves sound a checker of the
certificates Kater emits for its inclusion checks, and of the evidence its
saturations of the right-hand side record. With Lean installed
(through [elan](https://github.com/leanprover/elan)), `lake build` in
`formal/` checks the proofs, and the tests labeled `formal` run the checker
on the certificates of the suite:

```shell
cd Release && ctest -L formal
```

See [verification.md](verification.md) for what these check and what they
found.

Other helpers under `scripts/`:

 - `check-mirrors.sh`: reports the C++ that `formal/` mirrors in Lean and that
   changed since the Lean was last reviewed against it (the `check-mirrors`
   test); `--update` records it after the review. Every build runs it with
   `--warn`, which prints the reports as warnings and succeeds.

# Modifying Kater

## Pull requests

Please submit PRs as a series of atomic, easily reversible commits. Code must be
formatted with `clang-format` and free of `clang-tidy` warnings on the diff. Run:

```shell
./scripts/lint.sh           # uses the RelWithDebInfo build dir by default
```

`lint.sh` checks `clang-format` over all of `src/` and runs `clang-tidy` on the
changes relative to the merge base. Both checks gate CI.

## Source layout

`src/` is built as a stack of layers, each a static library that may depend
only on the layers below it:

| Layer (library)  | Files                                                        | Contract                                                              |
|------------------|--------------------------------------------------------------|-----------------------------------------------------------------------|
| `kater_support`  | `Config`, `Error`, `DbgInfo`, `Logger`, `VSet`, `AdjList`, `Visitor` | No crashes, no undefined behaviour                            |
| `kater_theory`   | `Predicate`, `Relation`, `TransLabel`, `Theory`              | Every structural fact (domains, inclusions, disjointness) holds in all executions |
| `kater_automata` | `NFA`, `NFAUtils`, `StatePair`, `Counterexample`, `Utils`    | Each operation keeps, or computes, exactly the stated language         |
| `kater_lang`     | `RegExp`, `Constraint`, `Statement`, `SavedExp`, `KatModule`, `Assumptions`, `Builtins`, the flex/bison parser | The parsed module means what the `.kat` text says; `RegExp::toNFA()` preserves the language |
| `kater_decision` | `Saturation`, `Checker`                                      | A "holds" verdict means the constraint holds under the theory and the assumptions |
| `kater_export`   | `Exporter`, `Printer`, `GenMCPrinter`, `CodeBuilder`         | The generated checker accepts exactly the consistent executions       |

`Checker` is the decision procedure and `Exporter` the code generator; the
exporter asks the checker to prove the side conditions its optimizations rely
on, never the other way round. `Theory` holds structural facts only; the
hypotheses stated as constraints (built-in and user `assume`s) live in
`Assumptions`, which folds the ones that are plain facts into the theory.

`scripts/check-layers.sh` verifies that no file includes a header from a layer
above its own, and runs as the `check-layers` ctest. When adding a file, add it
to its layer both in `src/CMakeLists.txt` and in that script.

## Code conventions

### Comments

Please use `/*` and `*/` as comment delimiters.

### Classes

- Declaration order within a class (public -> protected -> private):
  1. Types and type aliases
  2. Static constants/functions (e.g., factories)
  3. Ctors, assignment operators and dtor
  4. All other functions (ending with operators and friends)
  5. Data members (static -> nonstatic)

### Naming

- CamelCase for everything apart from things mimicking STL functionality
- Names start with a lowercase letter
- Member variables should end with an underscore (`_`)

### Assertions

Use `VERIFY(cond[, msg])` (`src/Error.hpp`) where breaking the invariant would
corrupt results silently, e.g. an ID used to index a vector: it stays on in
release builds, and under `KATER_DEBUG` it offers to attach a debugger. Use plain
`assert` elsewhere, and for checks whose cost grows with the automaton.

### Diagnostics

Build with `-DKATER_DEBUG=ON` to enable Kater's debug infrastructure. Use
`KATER_DEBUG(X)` / `DEBUG_WITH_TYPE(type, X)` (`src/Error.hpp`) for category-gated
debug output, and plain `assert` for invariants.
