/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# The superposition operator on bounded sequences

The Lyapunov–Perron method works in the Banach space `ℕ →ᵇ E` of bounded sequences (bounded
continuous functions on the discrete space `ℕ`, with the sup norm). A map `φ : E → G` acts on it
by composition, `x ↦ φ ∘ x` (the superposition, or Nemytskii, operator).

* `StableManifold.superpose φ`: the superposition operator, `superpose φ x n = φ (x n)` whenever
  `φ ∘ x` is bounded (`superpose_apply_of_bound`), in particular for every `x` when `φ` is
  Lipschitz (`superpose_apply_of_lipschitzWith`) or continuous on a proper space
  (`superpose_apply`); it is `0` otherwise, a junk value never used;
* `StableManifold.lipschitzWith_superpose`: a `K`-Lipschitz `φ` gives a `K`-Lipschitz operator;
* `StableManifold.continuous_superpose`: a continuous `φ` on a proper space gives a continuous
  operator;
* `StableManifold.applySeq`: the bounded bilinear map
  `(ℕ →ᵇ (E →L[ℝ] G)) × (ℕ →ᵇ E) → ℕ →ᵇ G`, `(a, y) ↦ (n ↦ a n (y n))`, through which the
  derivative of `superpose φ` is expressed (`StableManifold.Sequence.SuperposeContDiff`).

## Proofs (plan)

Size: 150–250 lines.

* `superpose_apply_of_bound`: unfold, `dif_pos`.
* `superpose_apply_of_lipschitzWith`: `‖φ (x n)‖ ≤ ‖φ 0‖ + K ‖x‖`
  (`LipschitzWith.dist_le_mul`, `BoundedContinuousFunction.norm_coe_le_norm`).
* `superpose_apply`: `φ` is bounded on the compact ball `closedBall 0 ‖x‖`
  (`isCompact_closedBall`, `IsCompact.exists_bound_of_continuousOn`).
* `lipschitzWith_superpose`: `‖φ (x n) - φ (y n)‖ ≤ K ‖x n - y n‖ ≤ K ‖x - y‖`, then
  `BoundedContinuousFunction.norm_le` (`LipschitzWith.of_dist_le_mul`).
* `continuous_superpose`: near `x`, all values `y n` with `‖y - x‖ < 1` lie in the compact ball
  `closedBall 0 (‖x‖ + 1)`, on which `φ` is uniformly continuous
  (`IsCompact.uniformContinuousOn_of_continuous`); so
  `‖superpose φ y - superpose φ x‖ ≤ sup_n ‖φ (y n) - φ (x n)‖` is small when `‖y - x‖` is.
-/

@[expose] public section

open Filter Topology Metric
open scoped NNReal

namespace StableManifold

open BoundedContinuousFunction

section Superpose

variable {E G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup G]

open Classical in
/-- The **superposition operator** of `φ` on bounded sequences: `x ↦ φ ∘ x` when `φ ∘ x` is
bounded (always the case when `φ` is Lipschitz, or continuous on a proper space); `0` otherwise,
a junk value. -/
noncomputable def superpose (φ : E → G) (x : ℕ →ᵇ E) : ℕ →ᵇ G :=
  if h : ∃ C, ∀ n, ‖φ (x n)‖ ≤ C then
    ofNormedAddCommGroupDiscrete (fun n ↦ φ (x n)) h.choose h.choose_spec
  else 0

theorem superpose_apply_of_bound {φ : E → G} {x : ℕ →ᵇ E} (h : ∃ C, ∀ n, ‖φ (x n)‖ ≤ C)
    (n : ℕ) : superpose φ x n = φ (x n) := by
  rw [superpose, dite_eq_left h]
  rfl

/-- For a Lipschitz `φ`, `superpose φ x n = φ (x n)` for every bounded sequence `x`. -/
theorem superpose_apply_of_lipschitzWith {φ : E → G} {K : ℝ≥0} (hφ : LipschitzWith K φ)
    (x : ℕ →ᵇ E) (n : ℕ) : superpose φ x n = φ (x n) := by
  sorry

/-- For a continuous `φ` on a proper space, `superpose φ x n = φ (x n)` for every bounded sequence
`x`. -/
theorem superpose_apply [ProperSpace E] {φ : E → G} (hφ : Continuous φ) (x : ℕ →ᵇ E) (n : ℕ) :
    superpose φ x n = φ (x n) := by
  sorry

theorem superpose_zero {φ : E → G} (hφ : φ 0 = 0) : superpose φ 0 = 0 := by
  sorry

/-- A `K`-Lipschitz `φ` gives a `K`-Lipschitz superposition operator. -/
theorem lipschitzWith_superpose {φ : E → G} {K : ℝ≥0} (hφ : LipschitzWith K φ) :
    LipschitzWith K (superpose φ) := by
  sorry

/-- A continuous `φ` on a proper space gives a continuous superposition operator.

Proof: `φ` is uniformly continuous on the compact ball `closedBall 0 (‖x‖ + 1)`, which contains
the values of all sequences `1`-close to `x`. -/
theorem continuous_superpose [ProperSpace E] {φ : E → G} (hφ : Continuous φ) :
    Continuous (superpose φ) := by
  sorry

end Superpose

section ApplySeq

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
  [NormedSpace ℝ G]

theorem norm_apply_apply_le (a : ℕ →ᵇ (E →L[ℝ] G)) (y : ℕ →ᵇ E) (n : ℕ) :
    ‖a n (y n)‖ ≤ ‖a‖ * ‖y‖ :=
  ((a n).le_opNorm (y n)).trans
    (mul_le_mul (a.norm_coe_le_norm n) (y.norm_coe_le_norm n) (norm_nonneg _) (norm_nonneg _))

/-- Pointwise application of a bounded sequence of operators to a bounded sequence of vectors,
`(a, y) ↦ (n ↦ a n (y n))`, as a bounded bilinear map. -/
noncomputable def applySeq : (ℕ →ᵇ (E →L[ℝ] G)) →L[ℝ] (ℕ →ᵇ E) →L[ℝ] (ℕ →ᵇ G) :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ
      (fun a y ↦ ofNormedAddCommGroupDiscrete (fun n ↦ a n (y n)) (‖a‖ * ‖y‖)
        (norm_apply_apply_le a y))
      (fun _ _ _ ↦ by ext; simp) (fun _ _ _ ↦ by ext; simp) (fun _ _ _ ↦ by ext; simp)
      (fun _ _ _ ↦ by ext; simp))
    1 (fun a y ↦ by
      rw [one_mul]
      exact norm_ofNormedAddCommGroup_le _ (by positivity) (norm_apply_apply_le a y))

@[simp]
theorem applySeq_apply (a : ℕ →ᵇ (E →L[ℝ] G)) (y : ℕ →ᵇ E) (n : ℕ) :
    applySeq a y n = a n (y n) :=
  rfl

theorem norm_applySeq_le (a : ℕ →ᵇ (E →L[ℝ] G)) : ‖applySeq a‖ ≤ ‖a‖ := by
  sorry

end ApplySeq

end StableManifold
