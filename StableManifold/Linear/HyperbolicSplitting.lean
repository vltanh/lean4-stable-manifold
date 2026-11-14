/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import StableManifold.Linear.Subspaces
public import Mathlib.LinearAlgebra.Projection

/-!
# Hyperbolic splittings with exponential estimates

`ContinuousLinearMap.HyperbolicSplitting A` bundles what the Lyapunov–Perron method needs about a
linear map `A` (an exponential dichotomy): the projection `P = S.proj` onto the stable subspace
along the unstable one, the inverse `B = S.unstableInv` of `A` on the unstable subspace (extended
by `0` on the stable subspace), and constants `C ≥ 1`, `0 < λ < 1` with

  `‖Aⁿ P‖ ≤ C λⁿ`, `‖Bⁿ (1 - P)‖ ≤ C λⁿ` for all `n`.

Everything is stated with endomorphisms of `E` (`*` is composition), so that the analysis never
meets subtypes.

* `HyperbolicSplitting.range_proj`, `HyperbolicSplitting.ker_proj`: the range of `P` is the
  stable subspace and its kernel the unstable one; so the splitting determines `P` and
  `IsCompl Eₛ Eᵤ` (`HyperbolicSplitting.isCompl`);
* `ContinuousLinearMap.nonempty_hyperbolicSplitting`: in finite dimension, a hyperbolic splitting
  exists as soon as `Eₛ` and `Eᵤ` are complementary (for instance when `A` is hyperbolic,
  `isCompl_stableSubspace_unstableSubspace`);
* `HyperbolicSplitting.bound = 3 C / (1 - λ)` and `HyperbolicSplitting.decayRate = (1 + λ) / 2`:
  the constants of the Lyapunov–Perron estimates (`StableManifold.Perron.Operator`).

## Proofs (plan)

Size: 300–450 lines. The algebraic identities are proved below or are one-line ring computations.

* `proj_apply_eq_zero_iff`: if `P x = 0`, then `n ↦ Bⁿ x` is a backward orbit
  (`A Bⁿ⁺¹ = (1 - P) Bⁿ`, `mul_unstableInv_pow_succ`) with `‖Bⁿ x‖ = ‖Bⁿ (1 - P) x‖ ≤ C λⁿ ‖x‖`;
  conversely, for a backward orbit `w` of `x`, `P x = Aⁿ P (w n)`, of norm `≤ C ‖w n‖ → 0`.
* `proj_apply_eq_self_iff`: if `P x = x` then `‖Aⁿ x‖ = ‖Aⁿ P x‖ ≤ C λⁿ ‖x‖`; conversely
  `Bⁿ Aⁿ (1 - P) = 1 - P` (induction from `B A = 1 - P`, `B (1 - P) = B`, `A P = P A`), so
  `‖(1 - P) x‖ = ‖Bⁿ (1 - P) Aⁿ x‖ ≤ C λⁿ ‖Aⁿ x‖ → 0`.
* `range_proj`, `ker_proj`, `isCompl`: from the two characterizations and `P² = P`
  (`LinearMap.isCompl_of_proj` for an idempotent, or directly `x = P x + (1 - P) x`).
* `nonempty_hyperbolicSplitting`: `P` is `Submodule.projection Eₛ Eᵤ h`, continuous in finite
  dimension (`LinearMap.toContinuousLinearMap`); `A P = P A` since `A` preserves both subspaces
  (`map_mem_stableSubspace`, `map_mem_unstableSubspace`, uniqueness of the decomposition,
  `Submodule.existsUnique_add_of_isCompl`). The restriction `Aₛ` of `A` to `Eₛ`
  (`ContinuousLinearMap.restrict`) has all orbits tending to `0`, so `‖Aₛⁿ‖ ≤ C₁ λ₁ⁿ`
  (`exists_norm_pow_le_mul_pow_of_tendsto`). The restriction `Aᵤ` to `Eᵤ` is bijective
  (`injOn_unstableSubspace`, `exists_mem_unstableSubspace_apply_eq`), hence a continuous linear
  equivalence (`LinearEquiv.ofBijective`, `LinearEquiv.toContinuousLinearEquiv`); the orbits of
  its inverse are the backward orbits, which tend to `0`, so `‖Aᵤ⁻ⁿ‖ ≤ C₂ λ₂ⁿ`. Then
  `B = ιᵤ Aᵤ⁻¹ πᵤ`, `Aⁿ P = ιₛ Aₛⁿ πₛ` and `Bⁿ (1 - P) = ιᵤ Aᵤ⁻ⁿ πᵤ` (with the inclusions `ι` and
  the projections `π = Submodule.projectionOnto`), so `C = max C₁ C₂ * max 1 (max ‖πₛ‖ ‖πᵤ‖)` and
  `λ = max λ₁ λ₂` work.
-/

@[expose] public section

open Filter Topology

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A **hyperbolic splitting** of `A` (an exponential dichotomy): a projection `P = proj`
commuting with `A`, a map `B = unstableInv` inverting `A` on the range of `1 - P` and vanishing on
the range of `P`, and exponential estimates `‖Aⁿ P‖ ≤ C λⁿ`, `‖Bⁿ (1 - P)‖ ≤ C λⁿ` with `C ≥ 1`
and `0 < λ < 1`. The range of `P` is then the stable subspace of `A` and its kernel the unstable
subspace (`HyperbolicSplitting.range_proj`, `HyperbolicSplitting.ker_proj`). -/
structure HyperbolicSplitting (A : E →L[ℝ] E) where
  /-- The projection onto the stable subspace along the unstable subspace. -/
  proj : E →L[ℝ] E
  /-- The inverse of `A` on the unstable subspace, extended by `0` on the stable subspace. -/
  unstableInv : E →L[ℝ] E
  /-- The constant `C` of the exponential estimates. -/
  const : ℝ
  /-- The rate `λ` of the exponential estimates. -/
  rate : ℝ
  proj_mul_proj : proj * proj = proj
  mul_proj_comm : A * proj = proj * A
  unstableInv_mul_proj : unstableInv * proj = 0
  proj_mul_unstableInv : proj * unstableInv = 0
  mul_unstableInv : A * unstableInv = 1 - proj
  unstableInv_mul : unstableInv * A = 1 - proj
  one_le_const : 1 ≤ const
  rate_pos : 0 < rate
  rate_lt_one : rate < 1
  norm_pow_mul_proj_le : ∀ n : ℕ, ‖A ^ n * proj‖ ≤ const * rate ^ n
  norm_unstableInv_pow_mul_le : ∀ n : ℕ, ‖unstableInv ^ n * (1 - proj)‖ ≤ const * rate ^ n

namespace HyperbolicSplitting

variable {A : E →L[ℝ] E} (S : A.HyperbolicSplitting)

/-- The constant `3 C / (1 - λ)` of the Lyapunov–Perron estimates: it bounds the norm of the
linear Lyapunov–Perron operator, also in the weighted norm with weights `decayRate ^ n`. -/
noncomputable def bound : ℝ := 3 * S.const / (1 - S.rate)

/-- The decay rate `(1 + λ) / 2 ∈ (λ, 1)` of the orbits on the stable manifold. -/
noncomputable def decayRate : ℝ := (1 + S.rate) / 2

theorem const_pos : 0 < S.const := zero_lt_one.trans_le S.one_le_const

theorem bound_pos : 0 < S.bound :=
  div_pos (by linarith [S.one_le_const]) (by linarith [S.rate_lt_one])

theorem rate_lt_decayRate : S.rate < S.decayRate := by
  unfold decayRate; linarith [S.rate_lt_one]

theorem decayRate_lt_one : S.decayRate < 1 := by
  unfold decayRate; linarith [S.rate_lt_one]

theorem decayRate_pos : 0 < S.decayRate := S.rate_pos.trans S.rate_lt_decayRate

theorem norm_proj_le : ‖S.proj‖ ≤ S.const := by
  simpa using S.norm_pow_mul_proj_le 0

theorem norm_one_sub_proj_le : ‖1 - S.proj‖ ≤ S.const := by
  simpa using S.norm_unstableInv_pow_mul_le 0

theorem unstableInv_mul_one_sub_proj : S.unstableInv * (1 - S.proj) = S.unstableInv := by
  rw [mul_sub, mul_one, S.unstableInv_mul_proj, sub_zero]

theorem one_sub_proj_mul_unstableInv : (1 - S.proj) * S.unstableInv = S.unstableInv := by
  rw [sub_mul, one_mul, S.proj_mul_unstableInv, sub_zero]

theorem proj_mul_one_sub_proj : S.proj * (1 - S.proj) = 0 := by
  rw [mul_sub, mul_one, S.proj_mul_proj, sub_self]

theorem one_sub_proj_mul_proj : (1 - S.proj) * S.proj = 0 := by
  rw [sub_mul, one_mul, S.proj_mul_proj, sub_self]

/-- `Aⁿ` commutes with `P`. -/
theorem pow_mul_proj_comm (n : ℕ) : A ^ n * S.proj = S.proj * A ^ n :=
  (Commute.pow_left S.mul_proj_comm n).eq

/-- `B Bⁿ⁺¹ = Bⁿ⁺¹ (1 - P)`, so `‖Bⁿ⁺¹‖ ≤ C λⁿ⁺¹`. -/
theorem norm_unstableInv_pow_succ_le (n : ℕ) :
    ‖S.unstableInv ^ (n + 1)‖ ≤ S.const * S.rate ^ (n + 1) := by
  have h : S.unstableInv ^ (n + 1) = S.unstableInv ^ (n + 1) * (1 - S.proj) := by
    rw [pow_succ, mul_assoc, S.unstableInv_mul_one_sub_proj]
  rw [h]
  exact S.norm_unstableInv_pow_mul_le (n + 1)

/-- `A Bⁿ⁺¹ = (1 - P) Bⁿ`: `n ↦ Bⁿ x` is a backward orbit of `(1 - P) x`. -/
theorem mul_unstableInv_pow_succ (n : ℕ) :
    A * S.unstableInv ^ (n + 1) = (1 - S.proj) * S.unstableInv ^ n := by
  rw [pow_succ', ← mul_assoc, S.mul_unstableInv]

/-- `P Bⁿ⁺¹ = 0`: the range of `B` lies in the kernel of `P`. -/
theorem proj_mul_unstableInv_pow_succ (n : ℕ) : S.proj * S.unstableInv ^ (n + 1) = 0 := by
  rw [pow_succ', ← mul_assoc, S.proj_mul_unstableInv, zero_mul]

/-- The fixed points of `P` are the vectors of the stable subspace.

Proof: `Aⁿ x = Aⁿ P x` decays; conversely `(1 - P) x = Bⁿ (1 - P) Aⁿ x → 0`. -/
theorem proj_apply_eq_self_iff {x : E} : S.proj x = x ↔ x ∈ A.stableSubspace := by
  sorry

/-- The kernel of `P` is the unstable subspace.

Proof: if `P x = 0`, `n ↦ Bⁿ x` is a backward orbit tending to `0`; conversely
`P x = Aⁿ P (w n)` for a backward orbit `w` of `x`. -/
theorem proj_apply_eq_zero_iff {x : E} : S.proj x = 0 ↔ x ∈ A.unstableSubspace := by
  sorry

/-- The range of `P` is the stable subspace. -/
theorem range_proj : LinearMap.range (S.proj : E →ₗ[ℝ] E) = A.stableSubspace := by
  sorry

/-- The kernel of `P` is the unstable subspace. -/
theorem ker_proj : LinearMap.ker (S.proj : E →ₗ[ℝ] E) = A.unstableSubspace := by
  sorry

/-- A hyperbolic splitting makes the stable and unstable subspaces complementary. -/
theorem isCompl : IsCompl A.stableSubspace A.unstableSubspace := by
  sorry

end HyperbolicSplitting

/-- **A hyperbolic splitting exists** in finite dimension when the stable and unstable subspaces
are complementary.

Proof: `P` is the projection onto `Eₛ` along `Eᵤ`; the restriction of `A` to `Eₛ` has
geometrically decaying powers (`exists_norm_pow_le_mul_pow_of_tendsto`), and the restriction to
`Eᵤ` is invertible with geometrically decaying inverse powers; `B` is that inverse composed with
the projection onto `Eᵤ`. -/
theorem nonempty_hyperbolicSplitting [FiniteDimensional ℝ E] {A : E →L[ℝ] E}
    (h : IsCompl A.stableSubspace A.unstableSubspace) : Nonempty A.HyperbolicSplitting := by
  sorry

end ContinuousLinearMap
