# leanproofs

Small Lean 4/mathlib proof project.

## Contents

- `Leanproofs/Fermat.lean` proves Fermat's little theorem for `ZMod p`, plus integer
  corollaries phrased as equalities in `ZMod p`.
- `Leanproofs/Basic.lean` is reserved for shared definitions used by future proofs.

## Development

This repository is pinned to Lean `v4.33.1` and mathlib `v4.33.1`.

```bash
lake build
```
