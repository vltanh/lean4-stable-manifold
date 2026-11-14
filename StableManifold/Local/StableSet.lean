/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import StableManifold.LocalSets
public import StableManifold.Linear.HyperbolicSplitting
public import StableManifold.Perron.Smooth
public import StableManifold.Local.Cutoff
public import Mathlib.Topology.Algebra.Group.Basic

/-!
# The local stable manifold

Let `f` be `Cⁿ` (`1 ≤ n ≤ ∞`) on a neighborhood of a fixed point `p` of a finite-dimensional real
normed space, and suppose that the stable and unstable subspaces `Eₛ`, `Eᵤ` of `A = Df(p)` are
complementary (for instance, `A` hyperbolic). Then there are `δ > 0` and a `Cⁿ` map
`hₛ : Eₛ → Eᵤ` with `hₛ 0 = 0`, `Dhₛ(0) = 0`, such that for **every** neighborhood `U` of `p`
inside the ball of radius `δ`, the local stable set of `f|_U` is the graph
`{p + x + hₛ x | x ∈ Vₛ}` over some neighborhood `Vₛ` of `0` in `Eₛ`
(`Function.exists_localStableSet_eq_graph_of_isCompl`). The map `hₛ` does not depend on `U`.

Ingredients:

* `StableManifold.localStableSet_eq_image_add`: translating the fixed point to `0`;
* `StableManifold.Perturbation.localStableSet_map_eq`: for a globally small Lipschitz perturbation
  `F = A + φ` and a bounded `U`, the local stable set of `F|_U` at `0` is the part of the global
  stable manifold whose forward orbit stays in `U` (a bounded orbit lies on the graph, and orbits
  on the graph tend to `0`);
* `StableManifold.Perturbation.stableGraph`: the graph map as a map `Eₛ → Eᵤ` between the
  subspaces, with its regularity and tangency (`contDiff_stableGraph`, `fderiv_stableGraph_zero`);
* `StableManifold.Perturbation.exists_localStableSet_map_eq_image`: for a bounded neighborhood `U`
  of `0`, the local stable set of `F|_U` is a graph over a neighborhood `Vₛ` of `0` in `Eₛ`
  (it contains the ball of radius `r / (2 C)` when `U` contains the ball of radius `r`, by the
  decay estimate `Perturbation.norm_iterate_le`).

## Proofs (plan)

Size: 300–450 lines.

* `localStableSet_eq_image_add`: `Function.localStableSet_conj` with the homeomorphism
  `Homeomorph.addLeft p`.
* `localStableSet_map_eq`: an orbit in the bounded `U` is bounded, so `(1 - P) x = graph x`
  (`bddOrbit_iff`); conversely such orbits tend to `0` (`tendsto_iterate`).
* `stableGraph`: `graph ξ ∈ Eᵤ` since `P (graph ξ) = 0` (`proj_graph`, `proj_apply_eq_zero_iff`).
  `contDiff_stableGraph`: `stableGraph = πᵤ ∘ graph ∘ ιₛ`, where `ιₛ = Eₛ.subtypeL` and `πᵤ` is a
  continuous linear projection onto `Eᵤ` (for instance `Submodule.projectionOnto Eᵤ Eₛ` made
  continuous by `LinearMap.toContinuousLinearMap`, with `S.isCompl`), identity on `Eᵤ`;
  `contDiff_graph`. `fderiv_stableGraph_zero`: the same composition and `hasFDerivAt_graph_zero`.
* `exists_localStableSet_map_eq_image`: take `Vₛ = {ξ | ∀ n, F^[n] (ξ + stableGraph ξ) ∈ U}`; a
  point `x` of `localStableSet_map_eq` is `P x + graph (P x)` with `P x ∈ Eₛ`
  (`range_proj`, `graph_proj`); `Vₛ` contains the ball of radius `r / (2 C)` by
  `norm_iterate_le` (`P ξ = ξ` on `Eₛ`, `proj_apply_eq_self_iff`).
* `Function.exists_localStableSet_eq_graph_of_isCompl`: `A = fderiv ℝ f p`, a splitting `S`
  (`nonempty_hyperbolicSplitting`); `g x = f (p + x) - p` is `Cⁿ` near `0` with derivative `A`
  (`HasFDerivAt.comp`, `ContDiffOn.comp`, `ContDiffAt.hasStrictFDerivAt`); cut off with
  `η = (1 / (2 S.bound)).toNNReal` (`exists_contDiff_lipschitzWith_eqOn_ball`) to get a
  `Perturbation S` equal to `g` on `ball 0 δ`, and `hₛ = stableGraph`. For `U ⊆ ball p δ`:
  `localStableSet_eq_image_add`, `Function.localStableSet_congr` (on `(p + ·) ⁻¹' U ⊆ ball 0 δ`),
  `exists_localStableSet_map_eq_image`, and `Set.image_image`.
-/

@[expose] public section

open Filter Topology Metric Set
open scoped NNReal

namespace StableManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Translation**: the local stable set of `f` at `p` is the translate by `p` of the local stable
set of `x ↦ f (p + x) - p` at `0`.

Proof: `Function.localStableSet_conj` with `Homeomorph.addLeft p`. -/
theorem localStableSet_eq_image_add (f : E → E) (p : E) (U : Set E) :
    Function.localStableSet f p U =
      (p + ·) '' Function.localStableSet (fun x ↦ f (p + x) - p) 0 ((p + ·) ⁻¹' U) := by
  sorry

namespace Perturbation

variable {A : E →L[ℝ] E} {S : A.HyperbolicSplitting} (F : Perturbation S)

/-- For a bounded `U`, the local stable set of `F|_U` at `0` is the part of the global stable
manifold whose forward orbit stays in `U`.

Proof: `bddOrbit_iff` and `tendsto_iterate`. -/
theorem localStableSet_map_eq {U : Set E} (hU : Bornology.IsBounded U) :
    Function.localStableSet F.map 0 U =
      {x | (1 - S.proj) x = F.graph x ∧ ∀ n, F.map^[n] x ∈ U} := by
  sorry

/-- The graph map as a map from the stable to the unstable subspace. -/
noncomputable def stableGraph (ξ : A.stableSubspace) : A.unstableSubspace :=
  ⟨F.graph ξ, S.proj_apply_eq_zero_iff.1 (F.proj_graph ξ)⟩

@[simp]
theorem coe_stableGraph (ξ : A.stableSubspace) : (F.stableGraph ξ : E) = F.graph ξ :=
  rfl

theorem stableGraph_zero : F.stableGraph 0 = 0 := by
  sorry

/-- The typed graph map is `Cⁿ` when `φ` is.

Proof: `stableGraph = πᵤ ∘ graph ∘ ιₛ` with continuous linear `πᵤ`, `ιₛ`; `contDiff_graph`. -/
theorem contDiff_stableGraph {n : ℕ∞} (hφ : ContDiff ℝ n F.φ) : ContDiff ℝ n F.stableGraph := by
  sorry

/-- The typed graph map has derivative `0` at `0` when `φ` has.

Proof: the same composition and `hasFDerivAt_graph_zero`. -/
theorem fderiv_stableGraph_zero (hφ : HasFDerivAt F.φ (0 : E →L[ℝ] E) 0) :
    fderiv ℝ F.stableGraph 0 = 0 := by
  sorry

/-- **The local stable set of the globalized map**: for a bounded neighborhood `U` of `0`, the
local stable set of `F|_U` at `0` is the graph of `stableGraph` over a neighborhood `Vₛ` of `0` in
the stable subspace.

Proof: `Vₛ = {ξ | ∀ n, F^[n] (ξ + stableGraph ξ) ∈ U}` (`localStableSet_map_eq`); it contains a
ball by the decay estimate `norm_iterate_le`. -/
theorem exists_localStableSet_map_eq_image {U : Set E} (hU : U ∈ 𝓝 0)
    (hUb : Bornology.IsBounded U) :
    ∃ Vs ∈ 𝓝 (0 : A.stableSubspace),
      Function.localStableSet F.map 0 U =
        (fun x : A.stableSubspace ↦ (x : E) + (F.stableGraph x : E)) '' Vs := by
  sorry

end Perturbation

end StableManifold

namespace Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The local stable manifold theorem**, for every small neighborhood. Let `f` be `Cⁿ`
(`1 ≤ n ≤ ∞`) on a neighborhood `W` of a fixed point `p`, and suppose that the stable and unstable
subspaces of `A = Df(p)` are complementary. Then there are `δ > 0` and a `Cⁿ` map
`hₛ : Eₛ → Eᵤ` with `hₛ 0 = 0` and `Dhₛ(0) = 0` such that, for every neighborhood `U` of `p`
inside the ball of radius `δ`, the local stable set of `f|_U` is the graph `{p + x + hₛ x}` over a
neighborhood `Vₛ` of `0` in `Eₛ`.

Proof: translate `p` to `0`, cut off (`StableManifold.exists_contDiff_lipschitzWith_eqOn_ball`),
and apply `StableManifold.Perturbation.exists_localStableSet_map_eq_image` to the globalized map,
which agrees with `f` on `U`. -/
theorem exists_localStableSet_eq_graph_of_isCompl {f : E → E} {p : E} {W : Set E} {n : ℕ∞}
    (hn : 1 ≤ n) (hW : W ∈ 𝓝 p) (hf : ContDiffOn ℝ n f W) (hfix : f p = p)
    (hsplit : IsCompl (fderiv ℝ f p).stableSubspace (fderiv ℝ f p).unstableSubspace) :
    ∃ δ > 0, ∃ hs : (fderiv ℝ f p).stableSubspace → (fderiv ℝ f p).unstableSubspace,
      ContDiff ℝ n hs ∧ hs 0 = 0 ∧ fderiv ℝ hs 0 = 0 ∧
      ∀ U ∈ 𝓝 p, U ⊆ ball p δ →
        ∃ Vs ∈ 𝓝 (0 : (fderiv ℝ f p).stableSubspace),
          localStableSet f p U = (fun x ↦ p + ↑x + ↑(hs x)) '' Vs := by
  sorry

end Function
