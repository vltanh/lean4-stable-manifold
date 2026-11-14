/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# The global Lipschitz cut-off

Let `g` be `Cⁿ` (`1 ≤ n ≤ ∞`) on a neighborhood of `0` in a finite-dimensional real normed space
`E`, with `g 0 = 0` and derivative `A` at `0`. For every `η > 0` there are `δ > 0` and a `Cⁿ` map
`φ : E → E`, globally `η`-Lipschitz, with `φ 0 = 0` and `Dφ(0) = 0`, such that `g = A + φ` on the
ball of radius `δ` (`StableManifold.exists_contDiff_lipschitzWith_eqOn_ball`). Thus near `0`, `g`
is a globally small Lipschitz perturbation of its linear part, to which the global theory
(`StableManifold.Perturbation`) applies.

* `StableManifold.exists_cutoff`: a smooth function `ρ : E → ℝ` with values in `[0, 1]`, equal to
  `1` on the closed unit ball and to `0` off the open ball of radius `2`, with bounded derivative;
* `StableManifold.exists_norm_fderiv_le_of_hasFDerivAt_zero`: a `C¹` map with `ψ 0 = 0` and
  `Dψ(0) = 0` satisfies `‖Dψ x‖ ≤ η` and `‖ψ x‖ ≤ η ‖x‖` on a small closed ball;
* `StableManifold.exists_contDiff_lipschitzWith_eqOn_ball`: the cut-off.

## Proofs (plan)

Size: 300–450 lines.

* `exists_cutoff`: the bump `ContDiffBump (0 : E)` with `rIn = 1`, `rOut = 2` (the instance
  `HasContDiffBump E` of finite dimension): `ContDiffBump.contDiff`,
  `ContDiffBump.one_of_mem_closedBall`, `ContDiffBump.zero_of_le_dist`, `ContDiffBump.nonneg`,
  `ContDiffBump.le_one`; its derivative is continuous (`ContDiff.continuous_fderiv`) with compact
  support (`ContDiffBump.hasCompactSupport`, `HasCompactSupport.fderiv`), hence bounded
  (`Continuous.bounded_above_of_compact_support`).
* `exists_norm_fderiv_le_of_hasFDerivAt_zero`: `ψ` is `C¹` on a neighborhood of `0`
  (`ContDiffOn.contDiffAt`, `ContDiffAt.eventually`), so `fderiv ℝ ψ` is continuous at `0`
  (`ContDiffAt.continuousAt_fderiv`) with value `0`; the bound on `ψ` follows from the mean value
  inequality on the convex ball (`Convex.norm_image_sub_le_of_norm_fderiv_le`).
* `exists_contDiff_lipschitzWith_eqOn_ball`: let `ψ = g - A` (derivative `0` at `0`), `M` bound
  `‖Dρ‖`, `η' = η / (2 M + 1)`, and `r` as in the previous lemma for `η'`, with
  `closedBall 0 r ⊆ interior W`; set `δ = r / 2` and `φ x = ρ (δ⁻¹ • x) • ψ x`.
  - `φ = ψ` on `ball 0 δ` (`ρ = 1` there), so `g = A + φ`; `φ 0 = 0`; `Dφ(0) = Dψ(0) = 0`
    (`HasFDerivAt.congr_of_eventuallyEq`).
  - `Cⁿ`: `contDiff_iff_contDiffAt`; on `interior W` it is a product of `Cⁿ` maps
    (`ContDiffAt.smul`, `ContDiffOn.contDiffAt`); on the open set `{x | 2 δ < ‖x‖}` it is `0`
    (`ContDiffAt.congr_of_eventuallyEq`, `contDiffAt_const`); the two sets cover `E` since
    `closedBall 0 (2 δ) ⊆ interior W`.
  - Lipschitz: `Dφ x = ρ (δ⁻¹ • x) • Dψ x + (δ⁻¹ • Dρ (δ⁻¹ • x)).smulRight (ψ x)`
    (`HasFDerivAt.smul`, `HasFDerivAt.comp`), so `‖Dφ x‖ ≤ η' + (M / δ) η' ‖x‖ ≤ η' (2 M + 1) = η`
    for `‖x‖ ≤ 2 δ`, and `Dφ x = 0` for `‖x‖ > 2 δ`; then `lipschitzWith_of_nnnorm_fderiv_le`.
-/

@[expose] public section

open Filter Topology Metric Set
open scoped NNReal

namespace StableManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A **smooth cut-off**: `ρ : E → ℝ`, `C^∞`, with values in `[0, 1]`, equal to `1` on the closed
unit ball and to `0` off the open ball of radius `2`, with bounded derivative.

Proof: a `ContDiffBump (0 : E)` with radii `1` and `2`; its derivative is continuous with compact
support. -/
theorem exists_cutoff :
    ∃ ρ : E → ℝ, (∀ m : ℕ∞, ContDiff ℝ m ρ) ∧ (∀ x, ‖x‖ ≤ 1 → ρ x = 1) ∧
      (∀ x, 2 ≤ ‖x‖ → ρ x = 0) ∧ (∀ x, 0 ≤ ρ x ∧ ρ x ≤ 1) ∧
      ∃ M, 0 ≤ M ∧ ∀ x, ‖fderiv ℝ ρ x‖ ≤ M := by
  sorry

/-- A `C¹` map near `0` with `ψ 0 = 0` and `Dψ(0) = 0` has, on a small closed ball inside the
interior of its domain, derivative of norm `≤ η` and values of norm `≤ η ‖x‖`.

Proof: continuity of `fderiv ℝ ψ` at `0`, and the mean value inequality on the ball. -/
theorem exists_norm_fderiv_le_of_hasFDerivAt_zero {ψ : E → E} {W : Set E} {n : ℕ∞} (hn : 1 ≤ n)
    (hW : W ∈ 𝓝 0) (hψ : ContDiffOn ℝ n ψ W) (hψ0 : ψ 0 = 0)
    (hdψ : HasFDerivAt ψ (0 : E →L[ℝ] E) 0) {η : ℝ} (hη : 0 < η) :
    ∃ r > 0, closedBall (0 : E) r ⊆ interior W ∧
      ∀ x ∈ closedBall (0 : E) r, ‖fderiv ℝ ψ x‖ ≤ η ∧ ‖ψ x‖ ≤ η * ‖x‖ := by
  sorry

/-- **The global Lipschitz cut-off.** Let `g` be `Cⁿ` (`1 ≤ n ≤ ∞`) on a neighborhood `W` of `0`,
with `g 0 = 0` and derivative `A` at `0`. For every `η > 0` there are `δ > 0` and a `Cⁿ` map
`φ : E → E`, globally `η`-Lipschitz, with `φ 0 = 0` and derivative `0` at `0`, such that
`g x = A x + φ x` on the ball of radius `δ`.

Proof: `φ x = ρ (δ⁻¹ • x) • (g x - A x)` with the cut-off `ρ` of `exists_cutoff` and `δ` small
(`exists_norm_fderiv_le_of_hasFDerivAt_zero`); its derivative has norm `≤ η` everywhere, so it is
`η`-Lipschitz (`lipschitzWith_of_nnnorm_fderiv_le`). -/
theorem exists_contDiff_lipschitzWith_eqOn_ball {g : E → E} {A : E →L[ℝ] E} {W : Set E}
    {n : ℕ∞} (hn : 1 ≤ n) (hW : W ∈ 𝓝 0) (hg : ContDiffOn ℝ n g W) (hg0 : g 0 = 0)
    (hA : HasFDerivAt g A 0) {η : ℝ≥0} (hη : 0 < η) :
    ∃ δ > 0, ∃ φ : E → E, ContDiff ℝ n φ ∧ LipschitzWith η φ ∧ φ 0 = 0 ∧
      HasFDerivAt φ (0 : E →L[ℝ] E) 0 ∧ EqOn g (fun x ↦ A x + φ x) (ball 0 δ) := by
  sorry

end StableManifold
