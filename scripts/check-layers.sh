#!/bin/bash
#
# Checks that no source file includes a header from a layer above its own.
#
# The layers are the ones src/CMakeLists.txt builds as libraries. A file may
# include headers from its own layer and the layers below it; anything else
# is reported and the script exits non-zero. A file not assigned to a layer
# is an error too, so new files have to be placed deliberately.
#
# Usage: ./scripts/check-layers.sh

set -uo pipefail

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
SRC="${SRC:-${DIR}/../src}"

declare -A LAYER_OF
assign() {
    local layer="$1"; shift
    for f in "$@"; do LAYER_OF["$f"]="$layer"; done
}

# Lower number: lower layer. Keep in sync with src/CMakeLists.txt.
assign 0 Config DbgInfo Error Logger AdjList VSet Visitor
assign 1 Predicate Relation Theory TransLabel
assign 2 Counterexample NFA NFAUtils StatePair Utils
assign 3 Assumptions Builtins Constraint KatModule ParsingDriver RegExp RegExpUtils SavedExp Statement Lexer Parser
assign 4 Checker Saturation
assign 5 CodeBuilder Exporter GenMCPrinter Printer
assign 6 main

rc=0
for path in "${SRC}"/*.cpp "${SRC}"/*.hpp "${SRC}"/*.lpp "${SRC}"/*.ypp; do
    file="$(basename "${path}")"
    stem="${file%.*}"
    if [[ -z "${LAYER_OF[$stem]+x}" ]]; then
        echo "${file}: not assigned to a layer"
        rc=1
        continue
    fi
    layer="${LAYER_OF[$stem]}"

    while read -r inc; do
        istem="${inc%.*}"
        # headers outside src/ (e.g. genmc/...) are not ours to layer
        [[ -z "${LAYER_OF[$istem]+x}" ]] && continue
        if (( LAYER_OF[$istem] > layer )); then
            echo "${file} (layer ${layer}) includes ${inc} (layer ${LAYER_OF[$istem]})"
            rc=1
        fi
    done < <(sed -nE 's/^[[:space:]]*#include[[:space:]]*"([^"/]+)".*/\1/p' "${path}")
done

if (( rc == 0 )); then
    echo "[layers] OK"
fi
exit "${rc}"
