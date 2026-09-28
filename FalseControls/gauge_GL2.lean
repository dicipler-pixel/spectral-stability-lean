import SpectralStability.Coupling
-- Deliberately false: a general invertible frame change B ↦ U B Uᵀ does not preserve the
-- spectrum. For U = diag(2, 1) and B = I the trace goes from 2 to 5.
example : (!![2, 0; 0, 1] * (1 : Matrix (Fin 2) (Fin 2) ℝ) *
    Matrix.transpose !![2, 0; 0, 1]).trace = (1 : Matrix (Fin 2) (Fin 2) ℝ).trace := by
  simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  norm_num
