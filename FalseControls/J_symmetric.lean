import SpectralStability.Basic
-- The symplectic factor is skew, not symmetric.
example : Matrix.transpose SpectralStability.J = SpectralStability.J := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [SpectralStability.J]
