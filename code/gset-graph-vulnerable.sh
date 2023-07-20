#!/bin/bash
FILEPATH=${1}
N=$(grep -Eo '[0-9]+' "${FILEPATH}" | sort -rn | head -n 1)
P=${2}
INFECTION=$(echo "scale=100;${N} * ${P}" | bc )
INFECTION=$(echo "${INFECTION%%.*}")

shuf -i 0-"${N}" -n "${INFECTION}" | sort -n | sed -e 's/^/!/' | cat