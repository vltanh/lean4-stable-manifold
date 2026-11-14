/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import StableManifold.Sequence.Superpose
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Smoothness of the superposition operator

Let `E` be a finite-dimensional real normed space and `φ : E → G` a `Cⁿ` map. Then the
superposition operator `x ↦ φ ∘ x` on the Banach space `ℕ →ᵇ E` of bounded sequences is `Cⁿ`
(`StableManifold.contDiff_superpose`, `n ≤ ∞`), with derivative
`D(superpose φ)(x) y = (n ↦ Dφ(x n) (y n))` (`StableManifold.hasFDerivAt_superpose`).

A bounded sequence takes its values in a compact ball of `E` (finite dimension), on which the
derivatives of `φ` are uniformly continuous; this is what makes the superposition operator
differentiable in the sup norm. No compact support or global bound on `φ` is needed.

* `StableManifold.exists_norm_sub_sub_fderiv_le`: the first-order Taylor remainder of a `C¹` map
  is `o(‖b‖)` uniformly for base points in a ball;
* `StableManifold.hasFDerivAt_superpose`, `StableManifold.fderiv_superpose`: the derivative;
* `StableManifold.contDiff_superpose`: `Cⁿ` regularity.

`E` and `G` live in the same universe, so that the induction on `n` can pass from `φ : E → G` to
`fderiv ℝ φ : E → (E →L[ℝ] G)` (that is all the applications need).

## Proofs (plan)

Size: 300–500 lines.

* `exists_norm_sub_sub_fderiv_le`: `fderiv ℝ φ` is continuous (`ContDiff.continuous_fderiv`),
  hence uniformly continuous on the compact ball `closedBall 0 (R + 1)`
  (`IsCompact.uniformContinuousOn_of_continuous`): take `δ ≤ 1` with
  `‖Dφ z - Dφ a‖ ≤ ε` when `‖z - a‖ < δ` in that ball. Apply the mean value inequality
  (`Convex.norm_image_sub_le_of_norm_fderiv_le`, on the segment `[a, a + b]`) to
  `z ↦ φ z - Dφ(a) z`, whose derivative is `Dφ z - Dφ a`.
* `hasFDerivAt_superpose`: with `R = ‖x‖`, the previous lemma gives, for `‖y‖ < δ`,
  `‖superpose φ (x + y) - superpose φ x - applySeq (superpose (fderiv ℝ φ) x) y‖ ≤ ε ‖y‖`
  (evaluate at each `n` with `superpose_apply`, `applySeq_apply`, then
  `BoundedContinuousFunction.norm_le`); this is `HasFDerivAt`
  (`hasFDerivAt_iff_isLittleO_nhds_zero`, `Asymptotics.isLittleO_iff`).
* `contDiff_superpose`: for `n : ℕ`, induction on `n` generalizing `G` (in universe `u`):
  `n = 0` is `continuous_superpose` (`contDiff_zero`); for `n + 1`, `contDiff_succ_iff_fderiv`,
  with `fderiv ℝ (superpose φ) = applySeq ∘ superpose (fderiv ℝ φ)` (`fderiv_superpose`),
  `applySeq` a continuous linear map (`ContinuousLinearMap.contDiff`, `ContDiff.comp`), and
  `superpose (fderiv ℝ φ)` of class `Cⁿ` by the induction hypothesis applied to
  `fderiv ℝ φ : E → (E →L[ℝ] G)`, which is `Cⁿ` (`ContDiff.fderiv_right`). For `n = ∞`,
  `contDiff_infty`.
-/

@[expose] public section

open Filter Topology Metric
open scoped NNReal BoundedContinuousFunction

universe u

namespace StableManifold

variable {E G : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **Uniform first-order Taylor estimate** for a `C¹` map: for base points `a` in the ball of
radius `R`, `‖φ (a + b) - φ a - Dφ(a) b‖ ≤ ε ‖b‖` as soon as `‖b‖ < δ`.

Proof: `Dφ` is uniformly continuous on `closedBall 0 (R + 1)`; mean value inequality for
`z ↦ φ z - Dφ(a) z` on the segment `[a, a + b]`. -/
theorem exists_norm_sub_sub_fderiv_le {φ : E → G} (hφ : ContDiff ℝ 1 φ) (R : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ a b : E, ‖a‖ ≤ R → ‖b‖ < δ →
      ‖φ (a + b) - φ a - fderiv ℝ φ a b‖ ≤ ε * ‖b‖ := by
  sorry

/-- **The derivative of the superposition operator**: for a `C¹` map `φ`, the superposition
operator has at `x` the derivative `y ↦ (n ↦ Dφ(x n) (y n))`.

Proof: `exists_norm_sub_sub_fderiv_le` with `R = ‖x‖`, evaluated at each `n`. -/
theorem hasFDerivAt_superpose {φ : E → G} (hφ : ContDiff ℝ 1 φ) (x : ℕ →ᵇ E) :
    HasFDerivAt (superpose φ) (applySeq (superpose (fderiv ℝ φ) x)) x := by
  sorry

theorem fderiv_superpose {φ : E → G} (hφ : ContDiff ℝ 1 φ) :
    fderiv ℝ (superpose φ) = fun x ↦ applySeq (superpose (fderiv ℝ φ) x) :=
  funext fun x ↦ (hasFDerivAt_superpose hφ x).fderiv

/-- **The superposition operator of a `Cⁿ` map is `Cⁿ`** on bounded sequences (`n ≤ ∞`).

Proof: induction on `n`, through `fderiv ℝ (superpose φ) = applySeq ∘ superpose (fderiv ℝ φ)`
and the induction hypothesis for `fderiv ℝ φ`; `contDiff_infty` for `n = ∞`. -/
theorem contDiff_superpose {φ : E → G} {n : ℕ∞} (hφ : ContDiff ℝ n φ) :
    ContDiff ℝ n (superpose φ) := by
  sorry

end StableManifold
