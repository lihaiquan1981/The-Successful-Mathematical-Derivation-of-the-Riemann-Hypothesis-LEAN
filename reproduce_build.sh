#!/bin/sh
# Li Haiquan
# Jilin University of Chemical Technology, China
# ORCID: https://orcid.org/0009-0000-7365-6535
# Email: lihaiquan@jluct.edu.cn
# Machine Verification of the Riemann Hypothesis · English-edition reproduction script
# Pinned versions: Lean 4.34.0-rc2 + mathlib v4.34.0-rc2
# Usage: on a machine with a mathlib4 workspace,
#   sh reproduce_build.sh /path/to/mathlib4
# Re-check passes iff every exit code is 0 and every #print axioms output is
# [propext, Classical.choice, Quot.sound].

set -e
M4=${1:-/tmp/mathlib4}
cd "$M4"
export LEAN_PATH="$M4"
D=$(dirname "$0")

for m in Lemma_9_5C Unitarity_Assembly Lemma_9_4 Theorem_9_5_Closure \
         Lemma_11_3 Final_Assembly Note_9_5B_mJet Final_Assembly_Unconditional \
         Lemma_9_5C_TaylorRemainder Theorem_9_3A MotherEquation_CoreVerification; do
  cp "$D/$m.lean" .
done

for m in Lemma_9_5C Unitarity_Assembly Lemma_9_4 Theorem_9_5_Closure \
         Lemma_11_3 Final_Assembly Note_9_5B_mJet Final_Assembly_Unconditional \
         Lemma_9_5C_TaylorRemainder Theorem_9_3A MotherEquation_CoreVerification; do
  lake env lean -o "$m.olean" -i "$m.ilean" "$m.lean" > "$m.log" 2>&1
  echo "$m exit: $?"
done
echo ALL_DONE
