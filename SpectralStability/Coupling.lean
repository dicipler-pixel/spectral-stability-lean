/-
Spectral Stability Across Obstruction Interfaces (Jeromie Beasley, 24 June 2026):
the coupling operator, the Fourier modes and Appendix A.

The paper's symplectic matrix is `J = [[0, -1], [1, 0]]`, written `Jp` here.

* Section 7.1: for a symmetric `M = [[a, b], [b, d]]`, the leading coupling block
  `MJ + JM` equals `(a + d) J`. It is skew, it depends only on the trace of `M`, it vanishes
  exactly on traceless `M`, and it does not vanish on isotropic `M = λI`.
* Section 10.4: the matrix `[[2b, d - a], [d - a, -2b]]` printed there is `MJ - JM`. It is
  symmetric and kills the isotropic part.
* Section 7.1: with `H₀` symmetric and `E` skew, the commutator is exactly
  `[H₀ + εE, (H₀ + εE)ᵀ] = 2ε [E, H₀]`, with no `ε²` term.
* Section 10.4, global gauge: a rotation `R` fixes `J` (`R J Rᵀ = J`) and the trace, so the
  leading block `tr(M) J` is unchanged when every `B_n` is rotated by the same `R`.
* Section 6: `J ξ± = ±i ξ±` for `ξ± = (1, ∓i)`, and the Fourier mode
  `ψ_n = e^{iθn} ξ±` satisfies `J(ψ_{n+1} - ψ_{n-1}) = ∓2 sin θ · ψ_n`, so
  `A` has eigenvalue `∓2α sin θ` at `θ = 2πk/N`.
* Appendix A, Lemma A.1: the weighted Cauchy–Schwarz step
  `(a + 2b + c)² ≤ 4(a² + 2b² + c²)`, the periodic shift sum, and the resulting bound
  `Σ eₙ² ≤ m² Σ xₙ²` when `0 ≤ eₙ ≤ (m/4)(x_{n+1} + 2xₙ + x_{n-1})`, i.e. `‖E_avg‖ ≤ max‖δB‖`.
-/
import Mathlib

namespace SpectralStability.Coupling

open Matrix Complex

/-- The paper's symplectic matrix `J = [[0, -1], [1, 0]]`. -/
def Jp : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

/-- A symmetric `2 × 2` matrix. -/
def symm2 (a b d : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a, b; b, d]

theorem Jp_transpose : Jpᵀ = -Jp := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Jp]

theorem Jp_sq : Jp * Jp = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Jp, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## Section 7.1 and 10.4: what the leading coupling block sees -/

/-- **The leading block is the trace times `J`.** `MJ + JM = (a + d) J`. -/
theorem anticomm_eq_trace (a b d : ℝ) :
    symm2 a b d * Jp + Jp * symm2 a b d = (a + d) • Jp := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [symm2, Jp, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- **The matrix printed in Section 10.4 is the commutator.**
`MJ - JM = [[2b, d - a], [d - a, -2b]]`. -/
theorem comm_formula (a b d : ℝ) :
    symm2 a b d * Jp - Jp * symm2 a b d = !![2 * b, d - a; d - a, -2 * b] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [symm2, Jp, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The leading block `MJ + JM` is skew for every symmetric `M`. -/
theorem anticomm_skew {n : Type*} [Fintype n] (M K : Matrix n n ℝ) (hM : Mᵀ = M)
    (hK : Kᵀ = -K) : (M * K + K * M)ᵀ = -(M * K + K * M) := by
  rw [transpose_add, transpose_mul, transpose_mul, hM, hK]
  simp only [neg_mul, mul_neg]
  abel

/-- The commutator `MJ - JM` is symmetric for every symmetric `M`. -/
theorem comm_symmetric {n : Type*} [Fintype n] (M K : Matrix n n ℝ) (hM : Mᵀ = M)
    (hK : Kᵀ = -K) : (M * K - K * M)ᵀ = M * K - K * M := by
  rw [transpose_sub, transpose_mul, transpose_mul, hM, hK]
  simp only [neg_mul, mul_neg]
  abel

/-- The leading block vanishes exactly on traceless gradients: anisotropy alone gives zero. -/
theorem anticomm_traceless (a b : ℝ) : symm2 a b (-a) * Jp + Jp * symm2 a b (-a) = 0 := by
  rw [anticomm_eq_trace]; simp

/-- On an isotropic gradient `M = λI` the leading block is `2λ J`, not zero. -/
theorem anticomm_isotropic (l : ℝ) : symm2 l 0 l * Jp + Jp * symm2 l 0 l = (2 * l) • Jp := by
  rw [anticomm_eq_trace]; ring_nf

/-- The commutator kills the isotropic part. -/
theorem comm_isotropic (l : ℝ) : symm2 l 0 l * Jp - Jp * symm2 l 0 l = 0 := by
  rw [comm_formula]; ext i j; fin_cases i <;> fin_cases j <;> simp

/-! ## Section 7.1: the commutator with a skew coupling is exactly first order -/

/-- **With a skew coupling the commutator is exactly `2ε [E, H₀]`.** -/
theorem skew_coupling_commutator {n : Type*} [Fintype n] (H E : Matrix n n ℝ) (hH : Hᵀ = H)
    (hE : Eᵀ = -E) (ε : ℝ) :
    (H + ε • E) * (H + ε • E)ᵀ - (H + ε • E)ᵀ * (H + ε • E) = (2 * ε) • (E * H - H * E) := by
  rw [transpose_add, transpose_smul, hH, hE, smul_neg, ← sub_eq_add_neg]
  simp only [add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul]
  module

/-- When the obstruction field is uniform the centered gradient is zero, so the leading block
vanishes. -/
theorem lead_uniform (B : Matrix (Fin 2) (Fin 2) ℝ) :
    (1 / 2 : ℝ) • ((B - B) * Jp + Jp * (B - B)) = 0 := by simp

/-! ## Section 10.4: invariance under one global rotation -/

/-- A rotation. -/
def rot (c s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![c, -s; s, c]

/-- A rotation fixes the symplectic matrix: `R J Rᵀ = J`. -/
theorem rot_fixes_J (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : rot c s * Jp * (rot c s)ᵀ = Jp := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rot, Jp, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [h]

/-- A rotation preserves the trace: `tr(R M Rᵀ) = tr M`. -/
theorem rot_trace (c s a b d : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    (rot c s * symm2 a b d * (rot c s)ᵀ).trace = (symm2 a b d).trace := by
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
  simp [rot, symm2]
  linear_combination (a + d) * h

/-- **The leading block is invariant under a global rotation.** Rotating the gradient by `R`
leaves `tr(M) J` unchanged. -/
theorem lead_rotation_invariant (c s a b d : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    (rot c s * symm2 a b d * (rot c s)ᵀ).trace • Jp = (a + d) • Jp := by
  rw [rot_trace c s a b d h]; simp [Matrix.trace_fin_two, symm2]

/-! ## Section 6: the symplectic Fourier modes -/

/-- The symplectic matrix over `ℂ`. -/
def Jc : Matrix (Fin 2) (Fin 2) ℂ := !![0, -1; 1, 0]

/-- `ξ₊ = (1, -i)`. -/
def ξp : Fin 2 → ℂ := ![1, -I]

/-- `ξ₋ = (1, i)`. -/
def ξm : Fin 2 → ℂ := ![1, I]

/-- `J ξ₊ = i ξ₊`. -/
theorem Jc_ξp : Jc *ᵥ ξp = I • ξp := by
  ext i; fin_cases i <;> simp [Jc, ξp, mulVec, dotProduct, Fin.sum_univ_two]

/-- `J ξ₋ = -i ξ₋`. -/
theorem Jc_ξm : Jc *ᵥ ξm = (-I) • ξm := by
  ext i; fin_cases i <;> simp [Jc, ξm, mulVec, dotProduct, Fin.sum_univ_two]

/-- The difference of phases: `(e^{iθ} - e^{-iθ}) i = -2 sin θ`. -/
theorem phase_difference (θ : ℂ) : (exp (θ * I) - exp (-θ * I)) * I = -2 * sin θ := by
  linear_combination two_sin θ

/-- The Fourier mode `ψ_n = e^{iθn} ξ`. -/
noncomputable def mode (θ : ℝ) (ξ : Fin 2 → ℂ) (n : ℤ) : Fin 2 → ℂ :=
  exp (θ * n * I) • ξ

theorem mode_shift (θ : ℝ) (ξ : Fin 2 → ℂ) (n : ℤ) :
    mode θ ξ (n + 1) - mode θ ξ (n - 1) =
      ((exp (θ * I) - exp (-θ * I)) * exp (θ * n * I)) • ξ := by
  have h1 : exp (θ * ((n + 1 : ℤ) : ℂ) * I) = exp (θ * I) * exp (θ * n * I) := by
    rw [← exp_add]; push_cast; ring_nf
  have h2 : exp (θ * ((n - 1 : ℤ) : ℂ) * I) = exp (-θ * I) * exp (θ * n * I) := by
    rw [← exp_add]; push_cast; ring_nf
  simp only [mode, h1, h2, ← sub_smul, sub_mul]

/-- **Section 6, the `+` branch.** `J(ψ_{n+1} - ψ_{n-1}) = -2 sin θ · ψ_n` for `ξ = ξ₊`, so
`A` has eigenvalue `-2α sin θ`. -/
theorem fourier_eigen_plus (θ : ℝ) (n : ℤ) :
    Jc *ᵥ (mode θ ξp (n + 1) - mode θ ξp (n - 1)) = (-2 * sin θ) • mode θ ξp n := by
  rw [mode_shift, mulVec_smul, Jc_ξp, smul_smul, ← phase_difference, mode, smul_smul]
  congr 1; ring

/-- **Section 6, the `−` branch.** For `ξ = ξ₋` the eigenvalue is `+2α sin θ`. -/
theorem fourier_eigen_minus (θ : ℝ) (n : ℤ) :
    Jc *ᵥ (mode θ ξm (n + 1) - mode θ ξm (n - 1)) = (2 * sin θ) • mode θ ξm n := by
  rw [mode_shift, mulVec_smul, Jc_ξm, smul_smul, mode, smul_smul]
  congr 1
  have := phase_difference θ
  linear_combination (-(exp (θ * n * I))) * this

/-! ## Appendix A, Lemma A.1 -/

/-- The weighted Cauchy–Schwarz step with weights `(1, 2, 1)`. -/
theorem weighted_cs (a b c : ℝ) : (a + 2 * b + c) ^ 2 ≤ 4 * (a ^ 2 + 2 * b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]

/-- The periodic shift sum: `Σ (x_{n+1} + 2xₙ + x_{n-1}) = 4 Σ xₙ`. -/
theorem shift_sum (N : ℕ) [NeZero N] (x : ZMod N → ℝ) :
    ∑ n, (x (n + 1) + 2 * x n + x (n - 1)) = 4 * ∑ n, x n := by
  have h1 : ∑ n, x (n + 1) = ∑ n, x n :=
    Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun _ => rfl)
  have h2 : ∑ n, x (n - 1) = ∑ n, x n :=
    Fintype.sum_equiv (Equiv.subRight 1) _ _ (fun _ => rfl)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, h1, h2, ← Finset.mul_sum]
  ring

/-- **Lemma A.1.** If every site obeys `0 ≤ eₙ ≤ (m/4)(x_{n+1} + 2xₙ + x_{n-1})` then `Σ eₙ² ≤ m² Σ xₙ²`: the averaging operator has norm at most `max‖δB‖`. -/
theorem lemma_A1 (N : ℕ) [NeZero N] (e x : ZMod N → ℝ) (m : ℝ) (he : ∀ n, 0 ≤ e n)
    (hbound : ∀ n, e n ≤ m / 4 * (x (n + 1) + 2 * x n + x (n - 1))) :
    ∑ n, e n ^ 2 ≤ m ^ 2 * ∑ n, x n ^ 2 := by
  have step : ∀ n, e n ^ 2 ≤
      m ^ 2 / 4 * (x (n + 1) ^ 2 + 2 * x n ^ 2 + x (n - 1) ^ 2) := by
    intro n
    have h0 := he n
    have h1 := hbound n
    have hsq : e n ^ 2 ≤ (m / 4 * (x (n + 1) + 2 * x n + x (n - 1))) ^ 2 :=
      pow_le_pow_left₀ h0 h1 2
    have hcs := weighted_cs (x (n + 1)) (x n) (x (n - 1))
    have hm : 0 ≤ m ^ 2 := sq_nonneg m
    calc e n ^ 2 ≤ (m / 4 * (x (n + 1) + 2 * x n + x (n - 1))) ^ 2 := hsq
      _ = m ^ 2 / 16 * (x (n + 1) + 2 * x n + x (n - 1)) ^ 2 := by ring
      _ ≤ m ^ 2 / 16 * (4 * (x (n + 1) ^ 2 + 2 * x n ^ 2 + x (n - 1) ^ 2)) := by
          gcongr
      _ = m ^ 2 / 4 * (x (n + 1) ^ 2 + 2 * x n ^ 2 + x (n - 1) ^ 2) := by ring
  calc ∑ n, e n ^ 2 ≤ ∑ n, m ^ 2 / 4 * (x (n + 1) ^ 2 + 2 * x n ^ 2 + x (n - 1) ^ 2) :=
        Finset.sum_le_sum (fun n _ => step n)
    _ = m ^ 2 / 4 * ∑ n, ((fun k => x k ^ 2) (n + 1) + 2 * (fun k => x k ^ 2) n +
          (fun k => x k ^ 2) (n - 1)) := by rw [Finset.mul_sum]
    _ = m ^ 2 * ∑ n, x n ^ 2 := by rw [shift_sum N (fun k => x k ^ 2)]; ring

end SpectralStability.Coupling
