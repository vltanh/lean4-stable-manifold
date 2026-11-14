/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import StableManifold.Linear.HyperbolicSplitting
public import StableManifold.Sequence.Superpose
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The linear Lyapunov–Perron operator

Let `S` be a hyperbolic splitting of `A` (projection `P`, unstable inverse `B`, constants `C`,
`λ`), on a real Banach space `E`. The bounded solutions `z` of the inhomogeneous linear equation

  `z (n + 1) = A (z n) + y n`

with a bounded right-hand side `y` are exactly the sequences `z = stableOrbit ξ + perronOp y`
(variation of constants), with

* `S.stableOrbit ξ n = Aⁿ (P ξ)` (`stableOrbit`, a bounded linear map `E → ℕ →ᵇ E`), and
* `S.perronOp y n = ∑_{k < n} A^(n-1-k) P (y k) - ∑_{j ≥ 0} B^(j+1) (y (n + j))` (`perronOp`, a
  bounded linear operator of `ℕ →ᵇ E`, the linear Lyapunov–Perron operator).

`ξ` fixes the stable component `P (z 0) = P ξ`. Main statements:

* `stableOrbit_add_perronOp_succ`, `proj_stableOrbit_add_perronOp_zero`:
  `stableOrbit ξ + perronOp y` solves the equation, with stable component `P ξ` at time `0`;
* `eq_stableOrbit_add_perronOp`: every bounded solution has this form, with `ξ = z 0`;
* `norm_perronOp_le`: `‖perronOp‖ ≤ S.bound = 3 C / (1 - λ)`;
* `norm_perronOp_apply_le_of_le`: the same bound in the weighted sup norm with weights
  `θⁿ`, `θ = S.decayRate = (1 + λ) / 2`: if `‖y n‖ ≤ M θⁿ` then
  `‖perronOp y n‖ ≤ S.bound * M * θⁿ`.

## Proofs (plan)

Size: 350–500 lines.

* `summable_unstableInv_pow_apply`: `‖B^(j+1) (y (n + j))‖ ≤ C λ^(j+1) ‖y‖`
  (`norm_unstableInv_pow_succ_le`), a geometric series (`Summable.of_norm_bounded`,
  `summable_geometric_of_lt_one`).
* `norm_perronTerm_le`: `∑_{k < n} C λ^(n-1-k) ≤ C / (1 - λ)` (`Finset.sum_range_reflect`,
  `Summable.sum_le_tsum`, `tsum_geometric_of_lt_one`) and `∑_j C λ^(j+1) ≤ C / (1 - λ)`
  (`norm_tsum_le_tsum_norm`); total `2 C / (1 - λ) ≤ S.bound`.
* `perronTerm_add`, `perronTerm_smul`: `Finset.sum_add_distrib`, `Summable.tsum_add`,
  `Summable.tsum_const_smul`, with the summability above.
* `norm_perronOp_le`: `LinearMap.mkContinuous_norm_le`.
* `norm_perronOp_apply_le_of_le`: with `θ - λ = (1 - λ) / 2`,
  `∑_{k<n} C λ^(n-1-k) M θ^k ≤ C M θⁿ / (θ - λ) = 2 C M θⁿ / (1 - λ)` and
  `∑_j C λ^(j+1) M θ^(n+j) ≤ C M θⁿ λ / (1 - λ θ) ≤ C M θⁿ / (1 - λ)`.
* `stableOrbit_add_perronOp_succ`: split into components. Stable part:
  `P z (n+1) = A^(n+1) P ξ + ∑_{k ≤ n} A^(n-k) P y k = A (P z n) + P y n`
  (`Finset.sum_range_succ`, `pow_mul_proj_comm`). Unstable part:
  `A (∑_j B^(j+1) y (n+j)) = ∑_j (1 - P) B^j y (n+j) = (1 - P) y n + ∑_j B^(j+1) y (n+1+j)`
  (`mul_unstableInv_pow_succ`, `one_sub_proj_mul_unstableInv`, `Summable.tsum_eq_zero_add`,
  `ContinuousLinearMap.map_tsum`).
* `eq_stableOrbit_add_perronOp`: the difference `d` of two bounded solutions with the same stable
  component at `0` solves `d (n + 1) = A (d n)`, so `P d n = Aⁿ P d 0 = 0` and
  `(1 - P) d n = Bᵐ (1 - P) d (n + m)`, of norm `≤ C λᵐ ‖d‖ → 0`; hence `d = 0`.
-/

@[expose] public section

open Filter Topology
open scoped BoundedContinuousFunction

namespace ContinuousLinearMap.HyperbolicSplitting

open BoundedContinuousFunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {A : E →L[ℝ] E}
  (S : A.HyperbolicSplitting)

/-- `‖Aⁿ P ξ‖ ≤ C λⁿ ‖P ξ‖`. -/
theorem norm_pow_apply_proj_le (n : ℕ) (ξ : E) :
    ‖(A ^ n) (S.proj ξ)‖ ≤ S.const * S.rate ^ n * ‖S.proj ξ‖ := by
  have h : (A ^ n) (S.proj ξ) = (A ^ n * S.proj) (S.proj ξ) := by
    rw [mul_apply_eq_comp, ← mul_apply_eq_comp S.proj S.proj, S.proj_mul_proj]
  rw [h]
  exact ((A ^ n * S.proj).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (S.norm_pow_mul_proj_le n) (norm_nonneg _))

/-- `‖Aⁿ P ξ‖ ≤ C ‖ξ‖`. -/
theorem norm_pow_apply_proj_le_const (n : ℕ) (ξ : E) :
    ‖(A ^ n) (S.proj ξ)‖ ≤ S.const * ‖ξ‖ := by
  rw [← mul_apply_eq_comp]
  refine ((A ^ n * S.proj).le_opNorm ξ).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  exact (S.norm_pow_mul_proj_le n).trans
    (mul_le_of_le_one_right S.const_pos.le (pow_le_one₀ S.rate_pos.le S.rate_lt_one.le))

/-- The **stable orbits** `ξ ↦ (n ↦ Aⁿ (P ξ))`, a bounded linear map into bounded sequences. -/
noncomputable def stableOrbit : E →L[ℝ] (ℕ →ᵇ E) :=
  LinearMap.mkContinuous
    { toFun := fun ξ ↦ ofNormedAddCommGroupDiscrete (fun n ↦ (A ^ n) (S.proj ξ)) (S.const * ‖ξ‖)
        fun n ↦ S.norm_pow_apply_proj_le_const n ξ
      map_add' := fun ξ η ↦ by ext n; simp
      map_smul' := fun c ξ ↦ by ext n; simp }
    S.const fun ξ ↦ norm_ofNormedAddCommGroup_le _ (by positivity [S.const_pos])
      fun n ↦ S.norm_pow_apply_proj_le_const n ξ

@[simp]
theorem stableOrbit_apply (ξ : E) (n : ℕ) : S.stableOrbit ξ n = (A ^ n) (S.proj ξ) :=
  rfl

theorem stableOrbit_proj (ξ : E) : S.stableOrbit (S.proj ξ) = S.stableOrbit ξ := by
  ext n
  simp only [stableOrbit_apply, ← mul_apply_eq_comp S.proj S.proj, S.proj_mul_proj]

/-- The `n`-th term of the linear Lyapunov–Perron operator:
`∑_{k < n} A^(n-1-k) P (y k) - ∑_{j ≥ 0} B^(j+1) (y (n + j))`. -/
noncomputable def perronTerm (y : ℕ → E) (n : ℕ) : E :=
  ∑ k ∈ Finset.range n, (A ^ (n - 1 - k)) (S.proj (y k)) -
    ∑' j : ℕ, (S.unstableInv ^ (j + 1)) (y (n + j))

variable [CompleteSpace E]

/-- The unstable series converges: `‖B^(j+1) (y (n + j))‖ ≤ C λ^(j+1) ‖y‖`. -/
theorem summable_unstableInv_pow_apply (y : ℕ →ᵇ E) (n : ℕ) :
    Summable fun j : ℕ ↦ (S.unstableInv ^ (j + 1)) (y (n + j)) := by
  sorry

/-- `‖perronTerm y n‖ ≤ 2 C / (1 - λ) ‖y‖ ≤ S.bound ‖y‖`. -/
theorem norm_perronTerm_le (y : ℕ →ᵇ E) (n : ℕ) : ‖S.perronTerm y n‖ ≤ S.bound * ‖y‖ := by
  sorry

theorem perronTerm_add (y z : ℕ →ᵇ E) (n : ℕ) :
    S.perronTerm ⇑(y + z) n = S.perronTerm y n + S.perronTerm z n := by
  sorry

theorem perronTerm_smul (c : ℝ) (y : ℕ →ᵇ E) (n : ℕ) :
    S.perronTerm ⇑(c • y) n = c • S.perronTerm y n := by
  sorry

/-- The **linear Lyapunov–Perron operator** on bounded sequences:
`perronOp y n = ∑_{k < n} A^(n-1-k) P (y k) - ∑_{j ≥ 0} B^(j+1) (y (n + j))`. -/
noncomputable def perronOp : (ℕ →ᵇ E) →L[ℝ] (ℕ →ᵇ E) :=
  LinearMap.mkContinuous
    { toFun := fun y ↦ ofNormedAddCommGroupDiscrete (S.perronTerm y) (S.bound * ‖y‖)
        (S.norm_perronTerm_le y)
      map_add' := fun y z ↦ by ext n; exact S.perronTerm_add y z n
      map_smul' := fun c y ↦ by ext n; exact S.perronTerm_smul c y n }
    S.bound fun y ↦ norm_ofNormedAddCommGroup_le _ (by positivity [S.bound_pos])
      (S.norm_perronTerm_le y)

theorem perronOp_apply (y : ℕ →ᵇ E) (n : ℕ) : S.perronOp y n = S.perronTerm y n :=
  rfl

/-- At time `0` only the unstable series remains. -/
theorem perronOp_apply_zero (y : ℕ →ᵇ E) :
    S.perronOp y 0 = -∑' j : ℕ, (S.unstableInv ^ (j + 1)) (y j) := by
  simp [perronOp_apply, perronTerm]

/-- The operator norm of the linear Lyapunov–Perron operator is at most `S.bound`. -/
theorem norm_perronOp_le : ‖S.perronOp‖ ≤ S.bound := by
  sorry

/-- **The weighted estimate**: if `‖y n‖ ≤ M θⁿ` with `θ = S.decayRate = (1 + λ) / 2`, then
`‖perronOp y n‖ ≤ S.bound * M * θⁿ`.

Proof: `∑_{k<n} C λ^(n-1-k) M θ^k ≤ 2 C M θⁿ / (1 - λ)` and
`∑_j C λ^(j+1) M θ^(n+j) ≤ C M θⁿ / (1 - λ)`. -/
theorem norm_perronOp_apply_le_of_le {y : ℕ →ᵇ E} {M : ℝ}
    (hy : ∀ n, ‖y n‖ ≤ M * S.decayRate ^ n) (n : ℕ) :
    ‖S.perronOp y n‖ ≤ S.bound * M * S.decayRate ^ n := by
  sorry

/-- The Lyapunov–Perron term vanishes on the stable component at time `0`. -/
theorem proj_perronOp_apply_zero (y : ℕ →ᵇ E) : S.proj (S.perronOp y 0) = 0 := by
  sorry

/-- `stableOrbit ξ + perronOp y` **solves** `z (n + 1) = A (z n) + y n`.

Proof: split into the stable component (finite sums) and the unstable one (the series, with
`A B^(j+1) = (1 - P) B^j`). -/
theorem stableOrbit_add_perronOp_succ (ξ : E) (y : ℕ →ᵇ E) (n : ℕ) :
    (S.stableOrbit ξ + S.perronOp y) (n + 1) =
      A ((S.stableOrbit ξ + S.perronOp y) n) + y n := by
  sorry

/-- The solution `stableOrbit ξ + perronOp y` has stable component `P ξ` at time `0`. -/
theorem proj_stableOrbit_add_perronOp_zero (ξ : E) (y : ℕ →ᵇ E) :
    S.proj ((S.stableOrbit ξ + S.perronOp y) 0) = S.proj ξ := by
  sorry

/-- **Every bounded solution** of `z (n + 1) = A (z n) + y n` is `stableOrbit (z 0) + perronOp y`.

Proof: the difference `d` solves `d (n + 1) = A (d n)` with `P (d 0) = 0`; so `P (d n) = 0` and
`(1 - P) (d n) = Bᵐ (1 - P) (d (n + m))` has norm `≤ C λᵐ ‖d‖ → 0`. -/
theorem eq_stableOrbit_add_perronOp {z y : ℕ →ᵇ E} (hz : ∀ n, z (n + 1) = A (z n) + y n) :
    z = S.stableOrbit (z 0) + S.perronOp y := by
  sorry

end ContinuousLinearMap.HyperbolicSplitting
