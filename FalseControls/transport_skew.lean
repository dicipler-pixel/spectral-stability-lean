import SpectralStability.Basic
open Matrix SpectralStability
-- Deliberately false: the transport operator J ⊗ Δ₁ is symmetric, not skew.
example : (Matrix.kroneckerMap (· * ·) J (Δ₁ 3))ᵀ = -(Matrix.kroneckerMap (· * ·) J (Δ₁ 3)) := by
  rw [← Matrix.kroneckerMap_transpose, J_skew, Δ₁_skew]
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [Matrix.kroneckerMap_apply, J, Δ₁, U]
