import SpectralStability.Coupling
open SpectralStability.Coupling
-- Deliberately false: the leading coupling block MJ + JM does not cancel an isotropic
-- gradient. For M = I it is 2J, not 0.
example : symm2 1 0 1 * Jp + Jp * symm2 1 0 1 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [symm2, Jp, Matrix.mul_apply, Fin.sum_univ_two]
