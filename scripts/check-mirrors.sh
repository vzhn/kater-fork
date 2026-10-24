#!/bin/bash
#
# Checks that the C++ that formal/ mirrors in Lean has not changed since
# formal/ was last reviewed against it.
#
# The mirrored code is marked by comments
#     /* formal: begin NAME, mirrored by LEAN-FILE */
#     ...
#     /* formal: end NAME */
# formal/mirrors.txt records the SHA-256 of each region's text without
# whitespace, so that reformatting does not count, as of the last review. A
# region that changed, appeared or disappeared is reported with the Lean to
# review against it. After the review (and any change to the Lean, which
# `ctest -L formal` then checks), --update records the regions as they are.
#
# With --warn, which every build runs, the reports are warnings and the
# script succeeds, printing nothing when formal/ is up to date; the ctest
# check-mirrors runs it without, and fails.
#
# Usage: ./scripts/check-mirrors.sh [--update | --warn]

set -uo pipefail

MODE="${1:-}"
case "${MODE}" in
"" | --update | --warn) ;;
*)
    echo "usage: $0 [--update | --warn]" >&2
    exit 2
    ;;
esac

# A report; a warning under --warn
report() {
    if [[ "${MODE}" == "--warn" ]]; then
        echo "warning: $1"
    else
        echo "$1"
    fi
}

# Reports that the check cannot run, and exits: with 0 under --warn, so that
# the build goes on
cannot() {
    report "formal/ cannot be checked against the C++ it mirrors: $1"
    [[ "${MODE}" == "--warn" ]] && exit 0
    exit 1
}

# The associative arrays below need bash 4 (macOS ships 3.2)
(( BASH_VERSINFO[0] >= 4 )) || cannot "scripts/check-mirrors.sh needs bash 4 or later"
if command -v sha256sum >/dev/null 2>&1; then
    sha256() { sha256sum | cut -d' ' -f1; }
elif command -v shasum >/dev/null 2>&1; then
    sha256() { shasum -a 256 | cut -d' ' -f1; }
else
    cannot "neither sha256sum nor shasum is installed"
fi

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
ROOT="$( cd "${DIR}/.." && pwd )"
MANIFEST="${ROOT}/formal/mirrors.txt"

# For each marked region: "REGION FILE NAME LEAN-FILE<tab>TEXT", the text
# without whitespace; "ERROR MESSAGE" for a malformed marker
regions() {
    grep -rlE --include='*.cpp' --include='*.hpp' 'formal: (begin|end) ' \
         "${ROOT}/src" "${ROOT}/tests" | sort |
    while read -r path; do
        awk -v file="${path#"${ROOT}"/}" '
            /formal: begin / {
                if (inside) {
                    print "ERROR " file ":" NR ": region " name " has no end"
                    exit
                }
                if (!match($0, /formal: begin [A-Za-z0-9_]+, mirrored by [^ ]+/)) {
                    print "ERROR " file ":" NR ": a begin marker without a name and a mirror"
                    exit
                }
                spec = substr($0, RSTART + 14, RLENGTH - 14)
                name = spec; sub(/,.*/, "", name)
                mirror = spec; sub(/.*mirrored by /, "", mirror)
                inside = 1; text = ""; next
            }
            /formal: end / {
                if (!inside || $0 !~ ("formal: end " name "([^A-Za-z0-9_]|$)")) {
                    print "ERROR " file ":" NR ": an end marker without its begin"
                    exit
                }
                print "REGION " file " " name " " mirror "\t" text
                inside = 0; next
            }
            inside { gsub(/[[:space:]]/, ""); text = text $0 }
            END {
                if (inside)
                    print "ERROR " file ": region " name " has no end"
            }
        ' "${path}"
    done
}

rc=0
current=""
while IFS=$'\t' read -r head text; do
    case "${head}" in
    ERROR*)
        report "${head#ERROR }"
        rc=1
        ;;
    REGION*)
        hash="$(printf '%s' "${text}" | sha256)"
        current+="${hash} ${head#REGION }"$'\n'
        ;;
    esac
done < <(regions)

if [[ "${MODE}" == "--update" ]]; then
    (( rc == 0 )) || exit 1
    {
        echo "# The C++ that formal/ mirrors in Lean, as of the last review of formal/"
        echo "# against it: the SHA-256 of each marked region without whitespace, its"
        echo "# file, its name, and the Lean that mirrors it. scripts/check-mirrors.sh"
        echo "# compares; after a review, scripts/check-mirrors.sh --update rewrites this."
        printf '%s' "${current}"
    } > "${MANIFEST}"
    echo "[mirrors] recorded $(grep -c . <<< "${current}") regions in formal/mirrors.txt"
    exit 0
fi

declare -A recorded
if [[ -f "${MANIFEST}" ]]; then
    while read -r hash file name _; do
        [[ -z "${hash}" || "${hash}" == \#* ]] && continue
        recorded["${file} ${name}"]="${hash}"
    done < "${MANIFEST}"
fi

declare -A seen
while read -r hash file name mirror; do
    [[ -z "${hash}" ]] && continue
    seen["${file} ${name}"]=1
    if [[ -z "${recorded["${file} ${name}"]+x}" ]]; then
        report "${file}: region ${name} is new: review ${mirror} against it"
        rc=1
    elif [[ "${recorded["${file} ${name}"]}" != "${hash}" ]]; then
        report "${file}: region ${name} changed: review ${mirror} against it"
        rc=1
    fi
done <<< "${current}"
for key in "${!recorded[@]}"; do
    if [[ -z "${seen["${key}"]+x}" ]]; then
        report "${key% *}: region ${key##* } is gone: review formal/ without it"
        rc=1
    fi
done

if (( rc == 0 )); then
    [[ "${MODE}" == "--warn" ]] || echo "[mirrors] OK"
elif [[ "${MODE}" == "--warn" ]]; then
    report "formal/ may no longer mirror the C++, and the ctest check-mirrors fails;"
    report "once formal/ agrees with the C++ again: ./scripts/check-mirrors.sh --update"
    exit 0
else
    echo "Once formal/ agrees with the C++ again: ./scripts/check-mirrors.sh --update"
fi
exit "${rc}"
