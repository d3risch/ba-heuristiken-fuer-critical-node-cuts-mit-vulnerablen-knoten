#!/bin/bash
N=${1}
P=${2}
INFECTION=$(echo "scale=100;${N} * ${P}" | bc )
INFECTION=$(echo "${INFECTION%%.*}")

shuf -i 0-"${N}" -n "${INFECTION}" | sort -n | sed -e 's/^/!/' | cat