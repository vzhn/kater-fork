#!/bin/bash
#
# Moves a vzhn/kater-fork issue or pull request to a column of the
# kater-fork board (https://github.com/users/vzhn/projects/4), adding it to
# the board first if it is not there yet.
#
# The column is a value of the board's Status field: Todo, In Progress,
# In Review or Done. Needs a gh token with the project scope
# (gh auth refresh -s project).
#
# Usage: ./scripts/board-move.sh <issue-or-pr-number> <column>
#   e.g. ./scripts/board-move.sh 46 "In Progress"

set -euo pipefail

OWNER=vzhn
REPO=vzhn/kater-fork
PROJECT=4

if [ $# -ne 2 ]; then
    echo "usage: $0 <issue-or-pr-number> <column>" >&2
    exit 2
fi
number="$1"
column="$2"

# gh issue view resolves pull request numbers too.
url=$(gh issue view "$number" -R "$REPO" --json url --jq .url)

project_id=$(gh project view "$PROJECT" --owner "$OWNER" --format json --jq .id)
read -r field_id option_id < <(
    gh project field-list "$PROJECT" --owner "$OWNER" --format json --jq \
        ".fields[] | select(.name == \"Status\") |
         \"\(.id) \(.options[] | select(.name == \"$column\") | .id)\"") || true
if [ -z "${option_id:-}" ]; then
    echo "no column \"$column\" on the board" >&2
    exit 1
fi

# Adding an item that is already on the board returns the existing one.
item_id=$(gh project item-add "$PROJECT" --owner "$OWNER" --url "$url" \
              --format json --jq .id)
gh project item-edit --project-id "$project_id" --id "$item_id" \
    --field-id "$field_id" --single-select-option-id "$option_id" >/dev/null
echo "#$number -> $column"
