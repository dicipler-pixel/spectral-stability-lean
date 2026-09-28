/-
Spectral Stability Across Obstruction Interfaces: results recovered from the earlier drafts
(The Obstruction Cascade, 18–21 June 2026), with a repair of the original mechanism.

* Cascade Theorem 4.1 (Algebraic Domination). If `Σ` is symmetric, `Σ m = λ_m m`,
  `m ⊥ n`, and `n` moves with `Σ` (`Σ' n + Σ n' = λ_n' n + λ_n n'`), then
  `⟨m|Σ'|n⟩ = (λ_n − λ_m) ⟨m|n'⟩`. So the connection form is the interband coupling divided by
  the gap, and it vanishes when the coupling vanishes across a nonzero gap.
* Cascade equation (9.4). If the transport part `A` is skew and the obstruction `D` is
  symmetric, then `[D + A, (D + A)ᵀ] = 2[A, D]`, so `D + A` is normal exactly when `A` and `D`
  commute.
* The repair. The centered difference `(Aψ)_n = α(ψ_{n+1} − ψ_{n−1})`, acting on each
  component, is skew on the periodic lattice, and its commutator with the obstruction field
  `(Dψ)_n = B_n ψ_n` is purely a gradient:
  `([A, D]ψ)_n = α((B_{n+1} − B_n) ψ_{n+1} − (B_{n−1} − B_n) ψ_{n−1})`.
  It vanishes when the field is uniform, and for `N ≥ 3` and `α ≠ 0` it vanishes only then.
  With this transport the drafts' Proposition 5.3, "non-normal exactly when the Hessians vary",
  holds as stated.
-/
import Mathlib

namespace SpectralStability.Recovered

open Matrix

/-! ## Cascade Theorem 4.1: the connection form is coupling over gap -/

/-- **Cascade Theorem 4.1.** `⟨m|Σ'|n⟩ = (λ_n − λ_m) ⟨m|n'⟩`. -/
theorem interband_coupling {k : Type*} [Fintype k] (S S' : Matrix k k ℝ) (hS : Sᵀ = S)
    (m v v' : k → ℝ) (lm lv lv' : ℝ) (hm : S *ᵥ m = lm • m) (hmv : m ⬝ᵥ v = 0)
    (hd : S' *ᵥ v + S *ᵥ v' = lv' • v + lv • v') :
    m ⬝ᵥ (S' *ᵥ v) = (lv - lm) * (m ⬝ᵥ v') := by
  have e := congrArg (fun w => m ⬝ᵥ w) hd
  simp only [dotProduct_add, dotProduct_smul, smul_eq_mul] at e
  have hsym : m ⬝ᵥ (S *ᵥ v') = lm * (m ⬝ᵥ v') := by
    rw [dotProduct_mulVec]
    conv_lhs => rw [← hS]
    rw [vecMul_transpose, hm, smul_dotProduct, smul_eq_mul]
  rw [hsym, hmv] at e
  linear_combination e

/-- **Algebraic domination.** Across a nonzero gap, zero interband coupling forces a zero
connection form. -/
theorem coupling_zero_connection_zero {k : Type*} [Fintype k] (S S' : Matrix k k ℝ)
    (hS : Sᵀ = S) (m v v' : k → ℝ) (lm lv lv' : ℝ) (hm : S *ᵥ m = lm • m)
    (hmv : m ⬝ᵥ v = 0) (hd : S' *ᵥ v + S *ᵥ v' = lv' • v + lv • v') (hgap : lv ≠ lm)
    (hzero : m ⬝ᵥ (S' *ᵥ v) = 0) : m ⬝ᵥ v' = 0 := by
  have h := interband_coupling S S' hS m v v' lm lv lv' hm hmv hd
  rw [hzero] at h
  rcases mul_eq_zero.mp h.symm with h0 | h0
  · exact absurd (sub_eq_zero.mp h0) hgap
  · exact h0

/-! ## Cascade equation (9.4): skew transport, symmetric obstruction -/

/-- **Cascade (9.4).** For skew `A` and symmetric `D`, `[D + A, (D + A)ᵀ] = 2[A, D]`. -/
theorem skew_transport_commutator {n : Type*} [Fintype n] (A D : Matrix n n ℝ) (hA : Aᵀ = -A)
    (hD : Dᵀ = D) :
    (D + A) * (D + A)ᵀ - (D + A)ᵀ * (D + A) = (2 : ℝ) • (A * D - D * A) := by
  rw [transpose_add, hA, hD]
  simp only [add_mul, mul_add, neg_mul, mul_neg, two_smul]
  abel

/-- With skew transport, the operator is normal exactly when transport and obstruction
commute. -/
theorem skew_transport_normal_iff {n : Type*} [Fintype n] (A D : Matrix n n ℝ)
    (hA : Aᵀ = -A) (hD : Dᵀ = D) :
    (D + A) * (D + A)ᵀ = (D + A)ᵀ * (D + A) ↔ A * D = D * A := by
  rw [← sub_eq_zero, skew_transport_commutator A D hA hD, smul_eq_zero, sub_eq_zero]
  simp

/-! ## The repair: plain centered difference on the periodic lattice -/

variable {N : ℕ}

/-- Plain centered difference on each component: `(Aψ)_n = α(ψ_{n+1} − ψ_{n−1})`. -/
def Adiff (α : ℝ) (ψ : ZMod N → Fin 2 → ℝ) : ZMod N → Fin 2 → ℝ :=
  fun n => α • (ψ (n + 1) - ψ (n - 1))

/-- The obstruction field `(Dψ)_n = B_n ψ_n`. -/
def Dop (B : ZMod N → Matrix (Fin 2) (Fin 2) ℝ) (ψ : ZMod N → Fin 2 → ℝ) :
    ZMod N → Fin 2 → ℝ :=
  fun n => B n *ᵥ ψ n

/-- The lattice inner product `⟨ψ, φ⟩ = Σ_n ψ_n · φ_n`. -/
def pair [NeZero N] (ψ φ : ZMod N → Fin 2 → ℝ) : ℝ := ∑ n, ψ n ⬝ᵥ φ n

/-- **The centered difference is skew** on the periodic lattice. -/
theorem adiff_skew [NeZero N] (α : ℝ) (ψ φ : ZMod N → Fin 2 → ℝ) :
    pair ψ (Adiff α φ) = -pair (Adiff α ψ) φ := by
  have h1 : ∑ n, ψ n ⬝ᵥ φ (n + 1) = ∑ n, ψ (n - 1) ⬝ᵥ φ n :=
    Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun x => by simp)
  have h2 : ∑ n, ψ n ⬝ᵥ φ (n - 1) = ∑ n, ψ (n + 1) ⬝ᵥ φ n :=
    Fintype.sum_equiv (Equiv.subRight 1) _ _ (fun x => by simp)
  simp only [pair, Adiff, dotProduct_smul, dotProduct_sub, smul_dotProduct, sub_dotProduct,
    smul_eq_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [h1, h2]
  ring

/-- **The obstruction field is symmetric** when every `B_n` is. -/
theorem dop_symmetric [NeZero N] (B : ZMod N → Matrix (Fin 2) (Fin 2) ℝ)
    (hB : ∀ n, (B n)ᵀ = B n) (ψ φ : ZMod N → Fin 2 → ℝ) :
    pair ψ (Dop B φ) = pair (Dop B ψ) φ := by
  unfold pair Dop
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [dotProduct_mulVec]
  conv_lhs => rw [← hB n]
  rw [vecMul_transpose]

/-- **The commutator is a pure gradient.**
`([A, D]ψ)_n = α((B_{n+1} − B_n) ψ_{n+1} − (B_{n−1} − B_n) ψ_{n−1})`. -/
theorem commutator_gradient (α : ℝ) (B : ZMod N → Matrix (Fin 2) (Fin 2) ℝ)
    (ψ : ZMod N → Fin 2 → ℝ) (n : ZMod N) :
    Adiff α (Dop B ψ) n - Dop B (Adiff α ψ) n =
      α • ((B (n + 1) - B n) *ᵥ ψ (n + 1) - (B (n - 1) - B n) *ᵥ ψ (n - 1)) := by
  simp only [Adiff, Dop, mulVec_smul, mulVec_sub, sub_mulVec, smul_sub]
  abel

/-- A uniform obstruction field commutes with the centered difference. -/
theorem uniform_commutes (α : ℝ) (B0 : Matrix (Fin 2) (Fin 2) ℝ) (ψ : ZMod N → Fin 2 → ℝ)
    (n : ZMod N) : Adiff α (Dop (fun _ => B0) ψ) n = Dop (fun _ => B0) (Adiff α ψ) n := by
  rw [← sub_eq_zero, commutator_gradient]
  simp

/-- A state supported on one site. -/
def bump (m : ZMod N) (v : Fin 2 → ℝ) : ZMod N → Fin 2 → ℝ :=
  fun k => if k = m then v else 0

/-- On a lattice of at least three sites, `n − 1 ≠ n + 1`. -/
theorem prev_ne_next (hN : 3 ≤ N) (n : ZMod N) : n - 1 ≠ n + 1 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod N) = 0 := by
    have : (2 : ZMod N) = (n + 1) - (n - 1) := by ring
    rw [Nat.cast_ofNat, this, h, sub_self]
  rw [ZMod.natCast_eq_zero_iff] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  omega

/-- **The drafts' Proposition 5.3, repaired.** On a lattice of at least three sites with
`α ≠ 0`, if the centered difference commutes with the obstruction field then the field is
uniform. -/
theorem commutes_forces_uniform (hN : 3 ≤ N) (α : ℝ) (hα : α ≠ 0)
    (B : ZMod N → Matrix (Fin 2) (Fin 2) ℝ)
    (h : ∀ ψ n, Adiff α (Dop B ψ) n = Dop B (Adiff α ψ) n) (n : ZMod N) :
    B (n + 1) = B n := by
  ext i j
  have hf := commutator_gradient α B (bump (n + 1) (Pi.single j 1)) n
  rw [h, sub_self] at hf
  have hne := prev_ne_next hN n
  have e1 : bump (n + 1) (Pi.single j (1 : ℝ)) (n + 1) = Pi.single j 1 := by simp [bump]
  have e2 : bump (n + 1) (Pi.single j (1 : ℝ)) (n - 1) = 0 := by simp [bump, hne]
  rw [e1, e2, mulVec_zero, sub_zero, mulVec_single_one] at hf
  have hi := congrFun hf i
  simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply,
    Matrix.sub_apply] at hi
  rcases mul_eq_zero.mp hi.symm with h0 | h0
  · exact absurd h0 hα
  · linarith

end SpectralStability.Recovered
