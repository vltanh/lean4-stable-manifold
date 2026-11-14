/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import StableManifold.Local.StableSet
public import StableManifold.Linear.Splitting
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# The stable manifold theorem for a hyperbolic fixed point

Let `f` be `Cⁿ` (`1 ≤ n ≤ ∞`) on a neighborhood of a fixed point `p` of a finite-dimensional real
normed space, with invertible and hyperbolic derivative `A = Df(p)`, and let `Eₛ`, `Eᵤ` be the
stable and unstable subspaces of `A`. Then there are an open neighborhood `U` of `p` and `Cⁿ` maps
`hₛ : Eₛ → Eᵤ`, `hᵤ : Eᵤ → Eₛ`, vanishing with their derivatives at `0`, such that the local stable
set of `f|_U` is the graph `{p + x + hₛ x}` of `hₛ` over a neighborhood of `0` in `Eₛ`, and the
local unstable set of `f|_U` is the graph `{p + y + hᵤ y}` of `hᵤ` over a neighborhood of `0` in
`Eᵤ` (`Function.exists_localStableSet_localUnstableSet_eq_graph`).

The unstable side is the stable side of the local inverse: `f` restricts to an open partial
homeomorphism `e` near `p` whose inverse is `Cⁿ` with derivative `A⁻¹` at `p`
(`Function.exists_openPartialHomeomorph_contDiffOn_symm`, the inverse function theorem); the
stable subspace of `A⁻¹` is the unstable subspace of `A` and conversely
(`ContinuousLinearMap.stableSubspace_symm`, `unstableSubspace_symm`), and the local unstable set
of `e|_U` is the local stable set of `e⁻¹|_U` (`Function.localStableSet_symm_eq_localUnstableSet`).
Since the local stable manifold theorem holds for every small neighborhood
(`Function.exists_localStableSet_eq_graph_of_isCompl`), one `U` serves for `f` and `e⁻¹`.

## Proofs (plan)

Size: 200–350 lines.

* `exists_openPartialHomeomorph_contDiffOn_symm`: `f` is `Cⁿ` at the points of `interior W`
  (`ContDiffOn.contDiffAt`), so `HasStrictFDerivAt f A p` (`ContDiffAt.hasStrictFDerivAt`, `n ≥ 1`)
  and `HasStrictFDerivAt.toOpenPartialHomeomorph` gives `e` with `⇑e = f`. Restrict its source to
  the open set of points of `interior W` where `fderiv ℝ f` is invertible
  (`OpenPartialHomeomorph.restrOpen`; openness from `ContinuousLinearEquiv.isOpen` and continuity of
  `fderiv ℝ f` on `interior W`, `ContDiffOn.continuousOn_fderiv_of_isOpen`). Then at each point `y`
  of the target, `OpenPartialHomeomorph.contDiffAt_symm` gives `ContDiffAt ℝ n e.symm y`, whence
  `ContDiffOn`; and `OpenPartialHomeomorph.hasFDerivAt_symm` (or
  `HasStrictFDerivAt.to_localInverse`) gives the derivative `A⁻¹` at `f p`. This is pointwise, so
  `n = ∞` needs no uniform neighborhood.
* `exists_graph_ofEq`: `subst` (proved below).
* `exists_localStableSet_localUnstableSet_eq_graph`: let `A = fderiv ℝ f p = ↑A'` (`hinv`) and
  `e` the local homeomorphism; `g = e.symm` is `Cⁿ` on `e.target ∈ 𝓝 p`, `g p = p`
  (`OpenPartialHomeomorph.left_inv`), `fderiv ℝ g p = ↑A'.symm` (`HasFDerivAt.fderiv`), so its
  stable and unstable subspaces are `Eᵤ` and `Eₛ`, complementary
  (`isCompl_stableSubspace_unstableSubspace`, `IsCompl.symm`). Apply
  `exists_localStableSet_eq_graph_of_isCompl` to `f` (radius `δ₁`, map `hₛ`) and to `g` (radius
  `δ₂`, map `hᵤ'`), and take `U = ball p (min δ₁ δ₂) ∩ e.source ∩ e.target`, open and containing
  `p`. The stable side is immediate. For the unstable side,
  `localUnstableSet f p U = localUnstableSet e p U` (`Function.localUnstableSet_congr`, `⇑e = f`)
  `= localStableSet e.symm p U` (`Function.localStableSet_symm_eq_localUnstableSet`), a graph of
  `hᵤ'` over the stable subspace of `fderiv ℝ g p`; transport it with `exists_graph_ofEq`.
-/

@[expose] public section

open Filter Topology Metric Set

namespace Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The local inverse** of a `Cⁿ` map with invertible derivative `A` at `p` (`1 ≤ n ≤ ∞`): an
open partial homeomorphism `e` with `⇑e = f` and `p` in its source, whose inverse is `Cⁿ` on its
target and has derivative `A⁻¹` at `f p`.

Proof: the inverse function theorem (`HasStrictFDerivAt.toOpenPartialHomeomorph`), with the source
restricted to the points where `f` is `Cⁿ` with invertible derivative, and
`OpenPartialHomeomorph.contDiffAt_symm` at each point of the target. -/
theorem exists_openPartialHomeomorph_contDiffOn_symm {f : E → E} {p : E} {W : Set E} {n : ℕ∞}
    (hn : 1 ≤ n) (hW : W ∈ 𝓝 p) (hf : ContDiffOn ℝ n f W) {A : E ≃L[ℝ] E}
    (hA : fderiv ℝ f p = A) :
    ∃ e : OpenPartialHomeomorph E E, (e : E → E) = f ∧ p ∈ e.source ∧
      ContDiffOn ℝ n e.symm e.target ∧ HasFDerivAt e.symm (A.symm : E →L[ℝ] E) (f p) := by
  sorry

omit [FiniteDimensional ℝ E] in
/-- A graph over a subspace is a graph over any equal subspace (to move between the subspaces of
`A⁻¹` and those of `A`, equal but not definitionally). -/
theorem exists_graph_ofEq {K₁ K₂ L₁ L₂ : Submodule ℝ E} (h₁ : K₁ = L₁) (h₂ : K₂ = L₂) {n : ℕ∞}
    {p : E} {s : Set E} {V : Set K₁} (hV : V ∈ 𝓝 0) {h : K₁ → K₂} (hh : ContDiffOn ℝ n h V)
    (h0 : h 0 = 0) (hd : fderiv ℝ h 0 = 0) (hs : s = (fun x ↦ p + ↑x + ↑(h x)) '' V) :
    ∃ V' ∈ 𝓝 (0 : L₁), ∃ h' : L₁ → L₂, ContDiffOn ℝ n h' V' ∧ h' 0 = 0 ∧ fderiv ℝ h' 0 = 0 ∧
      s = (fun x ↦ p + ↑x + ↑(h' x)) '' V' := by
  subst h₁ h₂
  exact ⟨V, hV, h, hh, h0, hd, hs⟩

/-- **The stable manifold theorem** for maps, in graph form (Irwin, *Smooth Dynamical Systems*,
Chapter 6; Hirsch, Pugh and Shub, *Invariant Manifolds*; Shub, *Global Stability of Dynamical
Systems*). Let `f` be `Cⁿ` (`1 ≤ n ≤ ∞`) on a neighborhood `W` of a fixed point `p`, with
invertible and hyperbolic derivative `A = Df(p)` (`f` is a local diffeomorphism at `p`), and let
`E_s`, `E_u` be the stable and unstable subspaces of `A`. Then there are an open neighborhood `U`
of `p` and `Cⁿ` maps `h_s : E_s → E_u`, `h_u : E_u → E_s`, vanishing with their derivatives at
`0`, such that

* the local stable set of `f|_U` is the graph `{p + x + h_s(x)}` of `h_s` over a neighborhood
  `V_s` of `0` in `E_s` (a `Cⁿ` embedded submanifold tangent at `p` to `E_s`), and
* the local unstable set of `f|_U` is the graph `{p + y + h_u(y)}` of `h_u` over a neighborhood
  `V_u` of `0` in `E_u` (a `Cⁿ` embedded submanifold tangent at `p` to `E_u`).

Proof: `exists_localStableSet_eq_graph_of_isCompl` for `f` and for its local inverse
(`exists_openPartialHomeomorph_contDiffOn_symm`), on a common small open neighborhood `U`, with
`localStableSet_symm_eq_localUnstableSet` and `stableSubspace_symm`, `unstableSubspace_symm`. -/
theorem exists_localStableSet_localUnstableSet_eq_graph {f : E → E} {p : E} {W : Set E}
    {n : ℕ∞} (hn : 1 ≤ n) (hW : W ∈ 𝓝 p) (hf : ContDiffOn ℝ n f W) (hfix : f p = p)
    (hinv : (fderiv ℝ f p).IsInvertible) (hyp : (fderiv ℝ f p).IsHyperbolic) :
    ∃ U ∈ 𝓝 p, IsOpen U ∧
      (∃ Vs ∈ 𝓝 (0 : (fderiv ℝ f p).stableSubspace),
        ∃ hs : (fderiv ℝ f p).stableSubspace → (fderiv ℝ f p).unstableSubspace,
          ContDiffOn ℝ n hs Vs ∧ hs 0 = 0 ∧ fderiv ℝ hs 0 = 0 ∧
          localStableSet f p U = (fun x ↦ p + ↑x + ↑(hs x)) '' Vs) ∧
      (∃ Vu ∈ 𝓝 (0 : (fderiv ℝ f p).unstableSubspace),
        ∃ hu : (fderiv ℝ f p).unstableSubspace → (fderiv ℝ f p).stableSubspace,
          ContDiffOn ℝ n hu Vu ∧ hu 0 = 0 ∧ fderiv ℝ hu 0 = 0 ∧
          localUnstableSet f p U = (fun y ↦ p + ↑y + ↑(hu y)) '' Vu) := by
  sorry

end Function
