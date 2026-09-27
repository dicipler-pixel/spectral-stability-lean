import SpectralStability.Basic
-- The commutator has a first-order term: for S = diag(1,0), E = e₁₂ it is ε·(nonzero), so
-- it cannot be purely second order. Its (0,0) entry at first order is 1, not 0.
example : ((!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.transpose !![0, 1; 0, 0]
    + !![0, 1; 0, 0] * !![1, 0; 0, 0] - !![1, 0; 0, 0] * !![0, 1; 0, 0]
    - Matrix.transpose !![0, 1; 0, 0] * !![1, 0; 0, 0]) = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
