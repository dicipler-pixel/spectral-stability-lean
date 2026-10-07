# What is not proved here

Lean proves exactly the statements written, under exactly the hypotheses written.

## Not formalized

* The resolvent perturbation estimate (Lemma 9.1), the Kreiss bounds, and the gluing theorems
  (Theorems 8.1 and 10.3, Corollaries 8.2 and 10.4). Corollary 9.2 is proved only as the
  scaling identity at `δ = c√ε`.
* Theorem 11.1 is proved on cubics, where the second difference is exact, and on `τ⁴`, where
  the error is exactly `δ²/12 · ψ⁗ = 2δ²`.
  The `L²` bound for general smooth, compactly supported `ψ` is not formalized.
* The Dunford–Taylor trace-log (Section 10), Proposition 10.1 (the continuum correspondence),
  the effective obstruction tensor and turning angle (Definition 10.2), the reporting metrics of
  Section 12, and the numerical sections.
* From the drafts: the cascade's Frobenius, degree and operator-algebra links (Lemma 4.2,
  Theorems 4.3 and 3.4 of *The Obstruction Cascade*) are not formalized; only Theorem 4.1 is.
* `Basic.lean` models the centered difference on an open chain (`Fin N`); the recovered module
  and the Fourier modes use the periodic lattice (`ZMod N`, or `ℤ`-indexed modes).
* Lemma A.1 is proved in its scalar form: it assumes the site-wise bound
  `‖(E_avg Ψ)ₙ‖ ≤ (m/4)(‖ψ_{n+1}‖ + 2‖ψₙ‖ + ‖ψ_{n−1}‖)` from the triangle inequality and
  concludes `‖E_avg Ψ‖ ≤ m ‖Ψ‖`.

## Where the Lean statement and the paper's wording differ

* **The leading coupling block.** `MJ + JM = tr(M) J` for every symmetric `2 × 2` `M`. The
  block therefore responds only to the isotropic part of the gradient and is zero on a traceless
  one. The matrix printed in Section 10.4 is `MJ − JM`, which is symmetric and responds only to
  the anisotropic part; a symmetric coupling alone would leave `H₀ + εE` symmetric.
* **Gauge.** One global rotation leaves the leading block, `A`, the anisotropy `Δₙ` and the
  spectrum unchanged. A site-dependent rotation changes `A`, and a general invertible
  `Uₙ ∈ GL(2)` acting by `Bₙ ↦ Uₙ Bₙ Uₙᵀ` changes the spectrum of `D₀` (false control
  `gauge_GL2`).
* **Transport.** `A = α J ⊗ Δ₁` is symmetric, as the final paper states. The 21 June draft's
  claim that it is skew is the false control `transport_skew`. The recovered module shows the
  drafts' mechanism, `[H, Hᵀ] = 2[A, D]`, holds when the transport is skew (the hypothesis of
  `skew_transport_commutator`), for example the plain centered difference.
* **Proposition 5.3 (drafts).** Two steps are proved separately. For the lattice operators
  `Adiff` and `Dop`, a uniform field commutes with the transport (`uniform_commutes`), and for
  `N ≥ 3`, `α ≠ 0` only a uniform field does (`commutes_forces_uniform`). For matrices with
  `Aᵀ = −A` and `Dᵀ = D`, `D + A` is normal exactly when `A` and `D` commute
  (`skew_transport_normal_iff`). `Adiff` and `Dop` are not written as matrices, so "non-normal
  exactly when the Hessians vary" is not a single Lean statement; the phrase "holds as stated"
  in `Recovered.lean` refers to these two steps.

## Wording in the Lean source comments

The `.lean` files are kept as verified at commit `cb9807b`, so these corrections are recorded here.

* `Coupling.lean` says the leading block vanishes "exactly" on traceless `M`.
  `anticomm_traceless` proves that it vanishes on traceless `M`; the converse is not stated as
  a theorem.
* `lead_uniform` writes the uniform field's centered gradient as `B − B`, so it holds
  immediately.
* `Basic.lean` defines `J = [[0, 1], [−1, 0]]`, the negative of the paper's
  `J = [[0, −1], [1, 0]]` (`Jp` in `Coupling.lean`). The skew and symmetric statements of
  Theorem 3.1 do not depend on this sign.
* The comment in `FalseControls/commutator_order_two.lean` names the `(0,0)` entry. The
  first-order term there is `[[0, −1], [−1, 0]]`: its `(0,1)` and `(1,0)` entries are `−1`, so
  the statement is false as intended.
