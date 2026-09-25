#!/usr/bin/env bash
set -euo pipefail

pattern='^[[:space:]]*(sorry|admit)[[:space:]]*$|:=[[:space:]]*(by[[:space:]]*)?(sorry|admit)([[:space:]]|$)|^[[:space:]]*axiom[[:space:]]|^[[:space:]]*unsafe[[:space:]]+(def|theorem)|(^|[^[:alnum:]_])native_decide([^[:alnum:]_]|$)'
mapfile -t matches < <(grep -RInE --include='*.lean' "$pattern" Lean4LeanModel Lean4LeanModel.lean || true)

unexpected=()
for match in "${matches[@]}"; do
  case "$match" in
    Lean4LeanModel/ModelConstructionDebt.lean:*':  sorry') ;;
    *) unexpected+=("$match") ;;
  esac
done

if ((${#unexpected[@]})); then
  echo 'Unexpected local proof debt:' >&2
  printf '  %s\n' "${unexpected[@]}" >&2
  exit 1
fi

debt_count=$(grep -cE '^[[:space:]]*sorry[[:space:]]*$' \
  Lean4LeanModel/ModelConstructionDebt.lean || true)
if [[ "$debt_count" != 3 ]]; then
  echo "Expected one known-false statement placeholder and two construction boundaries; found $debt_count holes" >&2
  exit 1
fi

# Keep reliance on upstream unique typing and its sorried inversion dependency auditable.
mapfile -t boundary_leaks < <(
  grep -RInE --include='*.lean' '\.uniq(U)?([[:space:](]|$)|IsDefEqU\.sort_inv|\.weakN_iff([[:space:](]|$)|\.skips(_iff)?([[:space:](]|$)|OnCtx\.weakN_inv|addInduct_WF|forallE_inv_stratified|sort_forallE_inv' \
    Lean4LeanModel --exclude='Upstream.lean' || true
)

if ((${#boundary_leaks[@]})); then
  echo 'Upstream metatheory escaped Lean4LeanModel/Upstream.lean:' >&2
  printf '  %s\n' "${boundary_leaks[@]}" >&2
  exit 1
fi

# Pin the complete transitive trust base of the headline theorem. In particular, this records that
# local and upstream proof debt is still visible as `sorryAx` instead of being hidden by a new axiom.
expected_axioms="'Lean4LeanModel.consistency' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]"
actual_axioms=$(lake env lean Lean4LeanModel/TrustAudit.lean 2>&1)
if [[ "$actual_axioms" != "$expected_axioms" ]]; then
  echo 'The consistency theorem trust base changed:' >&2
  printf '  expected: %s\n' "$expected_axioms" >&2
  printf '  actual:   %s\n' "$actual_axioms" >&2
  exit 1
fi
