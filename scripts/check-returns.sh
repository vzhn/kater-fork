#!/bin/bash
#
# Checks that every function of an exported checker that returns a value
# ends with a return statement, so that control cannot fall off its end
# (vzhn/kater-fork#51).
#
# It reads the layout GenMCPrinter prints: a function's declaration starts
# at the first column, its body opens and closes with "{" and "}" on lines
# of their own, and the statements of the body are indented by one tab.
# The last statement at that indentation has to be a return; a function
# that ended in an if-else returning from both branches would be reported,
# but the printer prints none.
#
# Usage: ./scripts/check-returns.sh FILE...

set -uo pipefail

if (( $# == 0 )); then
    echo "usage: $0 FILE..." >&2
    exit 2
fi

awk '
# The first line of the latest declaration, with its type and name
!body && /^[A-Za-z_[]/ { head = $0; line = FNR }
!body && /^\{$/ { body = 1; last = ""; next }
body && /^\}/ {
    body = 0
    type = head
    sub(/\(.*/, "", type)
    if (head !~ /\(/ || type ~ /(^|[[:space:]])void[[:space:]]/)
        next
    checked++
    if (last !~ /^\treturn([[:space:];]|$)/) {
        printf "%s:%d: %s ends without a return\n", FILENAME, line, head
        bad = 1
    }
    next
}
# A statement of the body, at its top level
body && /^\t[A-Za-z_[]/ { last = $0 }
END {
    # A layout this does not read would leave nothing checked
    if (!checked) {
        print "no function that returns a value found"
        exit 1
    }
    if (!bad)
        printf "[returns] OK: %d functions\n", checked
    exit bad
}
' "$@"
