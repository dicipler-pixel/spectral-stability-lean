<div align="center">

# Spectral Stability Across Obstruction Interfaces in Geometric Transport Systems — Lean proofs

[![Lean proof check](https://github.com/dicipler-pixel/spectral-stability-lean/actions/workflows/build.yml/badge.svg)](https://github.com/dicipler-pixel/spectral-stability-lean/actions/workflows/build.yml)
![Lean](https://img.shields.io/badge/Lean-v4.34.1-blue)
![Theorems](https://img.shields.io/badge/theorems-44-2EA043)
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
| Theorem 3.1 | The transport operator is Hermitian, so its spectrum is real (Lean states the Hermitian property; the real spectrum is the standard consequence, not restated) | `transport_hermitian` |
| Sec. 2 | `D₀ = diag(B_n)` with symmetric `B_n` is symmetric | `obstruction_symmetric` |
| Sec. 2 | At `ε = 0` the operator is normal; `[S + εE, (S + εE)ᵀ] = ε(SEᵀ + ES − SE − EᵀS) + ε²[E, Eᵀ]` | `symmetric_normal`, `commutator_expansion` |
| Corollary 9.2 | At `δ = c√ε` the correction `εΔ/δ²` is `Δ/c²` | `bulge_scaling` |
| Theorem 11.1 | The second difference is exact on cubics; on `τ⁴` its error is exactly `δ²/12 · ψ⁗` | `secondDiff_cubic`, `secondDiff_quartic` |

### The coupling operator, the Fourier modes and Appendix A

| Paper | Result | Theorem |
| :--- | :--- | :--- |
| Sec. 7.1 | For symmetric `M = [[a, b], [b, d]]` the leading block is `MJ + JM = (a + d) J`: skew, set by the trace alone, zero on traceless `M`, equal to `2λJ` on `M = λI` | `anticomm_eq_trace`, `anticomm_skew`, `anticomm_traceless`, `anticomm_isotropic` |
| Sec. 10.4 | The matrix `[[2b, d − a], [d − a, −2b]]` is `MJ − JM`; it is symmetric and zero on `M = λI` | `comm_formula`, `comm_symmetric`, `comm_isotropic` |
| Sec. 7.1 | With `H₀` symmetric and `E` skew, `[H₀ + εE, (H₀ + εE)ᵀ] = 2ε[E, H₀]` exactly | `skew_coupling_commutator` |
| Sec. 7.1 | A uniform field has centered gradient `B − B = 0`, so its leading block is zero (immediate) | `lead_uniform` |
| Sec. 10.4 | One global rotation fixes `J` and the trace, so it leaves the leading block unchanged | `rot_fixes_J`, `rot_trace`, `lead_rotation_invariant` |
| Sec. 6 | `J ξ± = ±i ξ±`, and the mode `ψₙ = e^{iθn} ξ±` has `J(ψ_{n+1} − ψ_{n−1}) = ∓2 sin θ · ψₙ`: eigenvalue `∓2α sin(2πk/N)` | `Jc_ξp`, `Jc_ξm`, `phase_difference`, `fourier_eigen_plus`, `fourier_eigen_minus` |
| App. A | `(a + 2b + c)² ≤ 4(a² + 2b² + c²)`, the periodic shift sum, and `‖E_avg‖ ≤ max‖δBₙ‖` | `weighted_cs`, `shift_sum`, `lemma_A1` |

### Recovered from the earlier drafts (18–21 June 2026)

| Draft | Result | Theorem |
| :--- | :--- | :--- |
| *The Obstruction Cascade*, Thm 4.1 | `⟨m|Σ'|n⟩ = (λₙ − λₘ)⟨m|n'⟩`: across a nonzero gap, zero interband coupling forces a zero connection form | `interband_coupling`, `coupling_zero_connection_zero` |
| Cascade eq. (9.4) | For skew `A` and symmetric `D`, `[D + A, (D + A)ᵀ] = 2[A, D]`, so `D + A` is normal exactly when `A` and `D` commute | `skew_transport_commutator`, `skew_transport_normal_iff` |
| Proposition 5.3 | With the plain centered difference (skew on the periodic lattice), the commutator with `D` is a pure gradient, it is zero for a uniform field, and for `N ≥ 3` and `α ≠ 0` it is zero only then. These are statements about the lattice operators; joining them with (9.4), which is stated for matrices, is not done in Lean | `adiff_skew`, `dop_symmetric`, `commutator_gradient`, `uniform_commutes`, `commutes_forces_uniform` |

The files are [`Basic.lean`](SpectralStability/Basic.lean),
[`Coupling.lean`](SpectralStability/Coupling.lean) and
[`Recovered.lean`](SpectralStability/Recovered.lean). What is not proved is in
[`LIMITATIONS.md`](LIMITATIONS.md); where each result came from is in
[`PROVENANCE.md`](PROVENANCE.md).

## How it is checked

Every push runs [the proof check](.github/workflows/build.yml): build against Lean v4.34.1 and
Mathlib v4.34.1, independent replay in Lean's kernel checker, an axiom audit (only `propext`,
`Classical.choice`, `Quot.sound`), and six deliberately false statements that must fail: `J` symmetric, a purely second-order commutator, the second difference exact on quartics, a general invertible frame change preserving the spectrum, the leading coupling block cancelling an isotropic gradient, and the transport operator being skew.

## The paper

*Spectral Stability Across Obstruction Interfaces in Geometric Transport Systems*, Jeromie Beasley. DOI
[10.5281/zenodo.20818899](https://doi.org/10.5281/zenodo.20818899) (always opens the newest version).

## Licence

Copyright (c) 2026 Jeromie Beasley. Code and proofs: [MIT](LICENSE). Written text:
[CC BY 4.0](LICENSE-CC-BY-4.0.md). See [`LICENSING.md`](LICENSING.md). Citation metadata is in
[`CITATION.cff`](CITATION.cff); how AI tools were used is stated in [`AI_USE.md`](AI_USE.md).
