# Changelog

Notable changes to Kater will be documented in this file.  This
repository is only updated whenever a new version of Kater is
released.

## [Unreleased]

### Fixes

- `lkmm-genmc.kat`: GenMC's prefix (`ppo`, `rppo`) no longer orders a
  fence before every later event (`[F] ; po`). Which fences a branch has
  depends on its path, and a prefix must not: a write after the join of a
  branch with a fence had the branch's read in its prefix, and could not
  revisit it, or a revisit kept the fence, which the new path never
  reached. GenMC re-adds a fence left out before the events a revisit
  kept, and checks the whole graph then (vzhn/genmc-fork#77)
- GenMC export: `getCoherentPlacings()` no longer offers, under a
  dependency-tracking model (IMM, LKMM), the placing right before the end
  of a store's range when that end is an RMW's write: the store then came
  between the write and the one its read reads (atomicity). GenMC counted
  such executions under some scheduling policies (vzhn/genmc-fork#237)

## [0.4.0-vzhn.3] - 2026.10.25

### Fixes

- `kat/lkmm-genmc.kat`: a fetch-and-op's write depends on its read, as
  herd7's `iico_data` has it (`rmw-data`, predicate `FopR`); GenMC allowed
  executions herd7 forbids, found by some scheduling policies only
  (vzhn/genmc-fork#237). `kat/lkmm-ref.kat` and `kater-oracle` follow (#69)

## [0.4.0-vzhn.2] - 2026.10.25

### Fixes

- GenMC export: an RMW read's own write part, and the reads of it, no
  longer stop a revisit of the read in `filterCoherentRevisits()` (the
  write part moves right after the revisiting write). genmc-fork carried
  this by hand in its LKMM checker; IMM's results do not change (#67)

## [0.4.0-vzhn.1] - 2026.10.25

The first release of the vzhn/kater-fork fork, on top of Kater 0.4.0.
genmc-fork's checkers are exported from it.

### Added

- Code export for GenMC's current checker interface and source layout
  (genmc-fork), and the Linux-kernel memory model (`kat/lkmm-genmc.kat`)
  with its error rules (#1, #63)
- `export nonextensible`: a model can say that an export is not
  extensible, and Kater's extensibility check of it only warns (#39)
- An extensibility check that decides (#33)
- `kater-oracle`: Kater and its exported checkers checked against a
  reference semantics; `tests/wrong` holds only false claims (#6, #31,
  #36, #42, #23)
- `formal/`: a checker of Kater's certificates and evidence, proved sound
  in Lean, and a build warning when the C++ it mirrors changes (#25, #26,
  #47, #48, #49, #57, #64)
- Kater split into verifiable layers (#5)

### Fixes

- Exact acyclicity checks in exported code, with Tarjan's algorithm (#27,
  #29)
- The check of a clause `A = 0` sets its counterexample (`cexLab`) (#34)
- Traversals of automata without states (#35), the check of
  `0 <= VIEW` (#51), counterexample completion (#37)
- The domain of an inverted relation (#45), two closure rules (#46),
  `total r`, a lost path in the predicate passes, a loop in
  `compactEdges` (#30), and the bugs `kater-oracle` found (#7-#18)

## [0.4.0] - 2026.09.02
### Added

- A number of performance optimizations, including antichain-based inclusion checking
- `cmake --install` now installs the `kater` binary
- Better diagnostics for code export
- Developer documentation (see `doc/development.md`) and clang-tidy config

### Changed

- Changed code export (e.g., for user-defined relations)
- A C++23 compiler is required
- flex/bison sources are generated out of tree

### Fixes

- Many bug fixes
- Properly resolve diamond and cyclic include paths

## [0.3.1] - 2025.11.11
### Changed

- Code export for GenMC updated (v0.14.1)

## [0.3] - 2024.09.03
### Added

- Support for mutually recursive relations via `let rec`
- Support for `extra` acyclicity exports

### Changed

- Using immediate relations (e.g., `po-imm`, `mo-imm`, etc) is now forbidden
- Different code export for GenMC

### Fixes

- Various bug fixes (e.g., for assertion checking)

## [0.2] - 2024.02.12
### Added

- Support for user-declared predicates via `predicate`
- Support for declaring pairwise disjoint predicates via `disjoint`
- Performance improvements
- clang-format file for project

### Changed

- User relations are now declared with `relation`
- Non-standard assumptions need to be of the form `[A];po;[B] <= [A];po;[F];po;[B]`
- The consistency-checking clauses of a KAT file now require the `export` prefix
- C++20 features are required for compilation
- Switch to `cmake` (instead of `autotools`)

### Fixes

- Various bug fixes
- Documentation fixes

## [0.1] - 2023.07.25
### Added

- Release on Github
