# Task board

Work on vzhn/kater-fork issues is tracked on the kater-fork board
(https://github.com/users/vzhn/projects/4), with the columns Todo,
In Progress and Done. Keep it current with `scripts/board-move.sh`:

- When you start work on an issue: `./scripts/board-move.sh <issue> "In Progress"`.
- When you file a new issue: `./scripts/board-move.sh <issue> Todo`.
- Write `Closes #<issue>` in the PR description; the board moves the issue
  to Done when the PR merges. Move it to Done yourself only for work that
  finishes without a PR.

If the script fails for a missing `project` scope, tell the user to run
`gh auth refresh -s project`; do not skip the move silently.
