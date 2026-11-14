/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import StableManifold

/-!
# Solution

Restates the four theorems of `StableManifoldChallenge.lean` word for word and proves them from
the library (`Function.exists_localStableSet_localUnstableSet_eq_graph`,
`ContinuousLinearMap.isCompl_stableSubspace_unstableSubspace`,
`ContinuousLinearMap.stableSubspace_symm`, `Function.localStableSet_symm_eq_localUnstableSet`).
The definitions that the statements use are those of `StableManifold.Defs`, of which the
Challenge carries a copy. Palomar's Comparator checks that these are the Challenge's statements
and that their proofs use only the standard axioms (`comparator.json`).
-/

public section

open Filter Topology

namespace StableManifoldChallenge

/-- **The stable manifold theorem** for a `Cⁿ` map (`1 ≤ n ≤ ∞`) near a fixed point `p` of a
finite-dimensional real normed space, with invertible and hyperbolic derivative `A = Df(p)`: there
are an open neighborhood `U` of `p` and maps `hₛ : Eₛ → Eᵤ`, `hᵤ : Eᵤ → Eₛ` between the stable and
unstable subspaces of `A`, `Cⁿ` near `0` and vanishing with their derivatives at `0`, such that the
local stable set of `f` in `U` is the graph `{p + x + hₛ x}` of `hₛ` over a neighborhood of `0` in
`Eₛ`, and the local unstable set of `f` in `U` is the graph `{p + y + hᵤ y}` of `hᵤ` over a
neighborhood of `0` in `Eᵤ`. -/
theorem stable_manifold {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → E} {p : E} {W : Set E} {n : ℕ∞} (hn : 1 ≤ n)
    (hW : W ∈ 𝓝 p) (hf : ContDiffOn ℝ n f W) (hfix : f p = p)
    (hinv : (fderiv ℝ f p).IsInvertible) (hyp : (fderiv ℝ f p).IsHyperbolic) :
    ∃ U ∈ 𝓝 p, IsOpen U ∧
      (∃ Vs ∈ 𝓝 (0 : (fderiv ℝ f p).stableSubspace),
        ∃ hs : (fderiv ℝ f p).stableSubspace → (fderiv ℝ f p).unstableSubspace,
          ContDiffOn ℝ n hs Vs ∧ hs 0 = 0 ∧ fderiv ℝ hs 0 = 0 ∧
          Function.localStableSet f p U = (fun x ↦ p + ↑x + ↑(hs x)) '' Vs) ∧
      (∃ Vu ∈ 𝓝 (0 : (fderiv ℝ f p).unstableSubspace),
        ∃ hu : (fderiv ℝ f p).unstableSubspace → (fderiv ℝ f p).stableSubspace,
          ContDiffOn ℝ n hu Vu ∧ hu 0 = 0 ∧ fderiv ℝ hu 0 = 0 ∧
          Function.localUnstableSet f p U = (fun y ↦ p + ↑y + ↑(hu y)) '' Vu) := by
  exact Function.exists_localStableSet_localUnstableSet_eq_graph hn hW hf hfix hinv hyp

/-- **The hyperbolic splitting**: the stable and unstable subspaces of a hyperbolic linear map `A`
of a finite-dimensional real normed space are complementary, `E = Eₛ ⊕ Eᵤ`. -/
theorem hyperbolic_splitting {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {A : E →L[ℝ] E} (hA : A.IsHyperbolic) :
    IsCompl A.stableSubspace A.unstableSubspace := by
  exact ContinuousLinearMap.isCompl_stableSubspace_unstableSubspace hA

/-- The stable subspace of the inverse of a linear isomorphism `e` is the unstable subspace of
`e`: `{v | e⁻ᵏ v → 0}` is the set of vectors with a backward `e`-orbit tending to `0`. -/
theorem stableSubspace_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : E ≃L[ℝ] E) :
    ContinuousLinearMap.stableSubspace (e.symm : E →L[ℝ] E) =
      ContinuousLinearMap.unstableSubspace (e : E →L[ℝ] E) := by
  exact ContinuousLinearMap.stableSubspace_symm e

/-- For a homeomorphism `e` between open sets and a set `U` inside its source and its target, the
local stable set of `e⁻¹` in `U` is the local unstable set of `e` in `U`. -/
theorem localStableSet_symm {X : Type*} [TopologicalSpace X] (e : OpenPartialHomeomorph X X)
    {p : X} {U : Set X} (hU : U ⊆ e.source ∩ e.target) :
    Function.localStableSet e.symm p U = Function.localUnstableSet e p U := by
  exact (Function.localStableSet_symm_eq_localUnstableSet e hU).1

end StableManifoldChallenge
