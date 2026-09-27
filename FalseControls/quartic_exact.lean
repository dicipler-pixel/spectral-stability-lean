import SpectralStability.Basic
-- The second difference is not exact on quartics: at δ = τ = 1 it gives 14, not 12.
example : SpectralStability.secondDiff (fun x => x ^ 4) 1 1 = 12 := by
  norm_num [SpectralStability.secondDiff]
