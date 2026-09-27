<div align="center">

# Spectral Stability Across Obstruction Interfaces in Geometric Transport Systems — Lean proofs

[![Lean proof check](https://github.com/dicipler-pixel/spectral-stability-lean/actions/workflows/build.yml/badge.svg)](https://github.com/dicipler-pixel/spectral-stability-lean/actions/workflows/build.yml)
![Lean](https://img.shields.io/badge/Lean-v4.34.1-blue)
![Theorems](https://img.shields.io/badge/theorems-11-2EA043)
![sorry](https://img.shields.io/badge/sorry-0-2EA043)
![Code: MIT](https://img.shields.io/badge/code-MIT-lightgrey)
![Text: CC BY 4.0](https://img.shields.io/badge/text-CC%20BY%204.0-lightgrey)
[![Paper DOI](https://img.shields.io/badge/paper-10.5281%2Fzenodo.20818899-blue)](https://doi.org/10.5281/zenodo.20818899)

Jeromie Beasley

</div>

---

## The idea in one line

`H_N(ε) = A + D₀ + εE`. The transport part `A = α J ⊗ Δ₁` is a product of two skew factors
acting on independent indices, so it is symmetric and its spectrum is real. The obstruction
field is symmetric too, so every departure from normality comes from `εE`, and it starts at
first order in `ε`.

## What is proved

| Paper | Result | Theorem |
| :--- | :--- | :--- |
| Theorem 3.1 | `J` and `Δ₁ = U − Uᵀ` are skew; `(α J ⊗ Δ₁)ᵀ = α J ⊗ Δ₁`; two commuting skew matrices have a symmetric product | `J_skew`, `Δ₁_skew`, `transport_symmetric`, `skew_commuting_symmetric` |
| Theorem 3.1 | The transport operator is Hermitian, so its spectrum is real | `transport_hermitian` |
| Sec. 2 | `D₀ = diag(B_n)` with symmetric `B_n` is symmetric | `obstruction_symmetric` |
| Sec. 2 | At `ε = 0` the operator is normal; `[S + εE, (S + εE)ᵀ] = ε(SEᵀ + ES − SE − EᵀS) + ε²[E, Eᵀ]` | `symmetric_normal`, `commutator_expansion` |
| Corollary 9.2 | At `δ = c√ε` the correction `εΔ/δ²` is `Δ/c²` | `bulge_scaling` |
| Theorem 11.1 | The second difference is exact on cubics; on `τ⁴` its error is exactly `δ²/12 · ψ⁗` | `secondDiff_cubic`, `secondDiff_quartic` |

The file is [`SpectralStability/Basic.lean`](SpectralStability/Basic.lean). What is not proved is
in [`LIMITATIONS.md`](LIMITATIONS.md).

## How it is checked

Every push runs [the proof check](.github/workflows/build.yml): build against Lean v4.34.1 and
Mathlib v4.34.1, independent replay in Lean's kernel checker, an axiom audit (only `propext`,
`Classical.choice`, `Quot.sound`), and three deliberately false statements that must fail.

## The paper

*Spectral Stability Across Obstruction Interfaces in Geometric Transport Systems*, Jeromie Beasley. DOI
[10.5281/zenodo.20818899](https://doi.org/10.5281/zenodo.20818899) (always opens the newest version).

## Licence

Copyright (c) 2026 Jeromie Beasley. Code and proofs: [MIT](LICENSE). Written text:
[CC BY 4.0](LICENSE-CC-BY-4.0.md). See [`LICENSING.md`](LICENSING.md). Citation metadata is in
[`CITATION.cff`](CITATION.cff); how AI tools were used is stated in [`AI_USE.md`](AI_USE.md).
