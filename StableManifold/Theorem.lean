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

## Proofs

* `exists_openPartialHomeomorph_contDiffOn_symm`: `f` is `Cⁿ` at every point of `interior W`
  (`ContDiffOn.contDiffAt`), so the inverse function theorem
  (`ContDiffAt.toOpenPartialHomeomorph`) gives an open partial homeomorphism `e₀` with `⇑e₀ = f`
  and `p` in its source. Its source is then restricted (`OpenPartialHomeomorph.restrOpen`) to the
  points of `interior W` where `fderiv ℝ f` is invertible, an open set since `fderiv ℝ f` is
  continuous there (`ContDiffOn.continuousOn_fderiv_of_isOpen`,
  `ContinuousLinearMap.isOpen_setOfPred_isInvertible`). At each point of the target,
  `OpenPartialHomeomorph.contDiffAt_symm` makes `e.symm` of class `Cⁿ`; the argument is
  pointwise, so `n = ∞` needs no uniform neighborhood. The derivative `A⁻¹` of `e.symm` at `f p`
  comes from `HasStrictFDerivAt.to_localInverse`.
* `exists_graph_ofEq`: `subst`.
* `exists_localStableSet_localUnstableSet_eq_graph`: write `fderiv ℝ f p = ↑A` (`hinv`) and let
  `e` be the local inverse above. Then `e.symm` fixes `p` (`OpenPartialHomeomorph.left_inv`) and
  has derivative `A⁻¹` there (`HasFDerivAt.fderiv`), so its stable and unstable subspaces are `Eᵤ`
  and `Eₛ` (`ContinuousLinearMap.stableSubspace_symm`, `unstableSubspace_symm`), complementary by
  `isCompl_stableSubspace_unstableSubspace` and `IsCompl.symm`. Apply
  `exists_localStableSet_eq_graph_of_isCompl` to `f` (radius `δ₁`, map `hₛ`) and to `e.symm` on
  `e.target` (radius `δ₂`, map `hᵤ`), and take `U = ball p (min δ₁ δ₂) ∩ e.source ∩ e.target`,
  open and containing `p`. The stable side follows at once (`ContDiff.contDiffOn`). For the
  unstable side, `localUnstableSet f p U = localUnstableSet e p U`
  (`Function.localUnstableSet_congr`, as `⇑e = f`) `= localStableSet e.symm p U`
  (`Function.localStableSet_symm_eq_localUnstableSet`, as `U ⊆ e.source ∩ e.target`), the graph
  of `hᵤ` over a neighborhood of `0` in the stable subspace of `fderiv ℝ e.symm p`;
  `exists_graph_ofEq` makes it a graph over `Eᵤ` with values in `Eₛ`.
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
  have hn0 : (n : WithTop ℕ∞) ≠ 0 := by
    have : (0 : ℕ∞) < n := zero_lt_one.trans_le hn
    exact_mod_cast this.ne'
  have hn1 : (1 : WithTop ℕ∞) ≤ n := by exact_mod_cast hn
  have hfa (x : E) (hx : x ∈ interior W) : ContDiffAt ℝ n f x :=
    hf.contDiffAt (mem_interior_iff_mem_nhds.1 hx)
  have hfd (x : E) (hx : x ∈ interior W) : HasFDerivAt f (fderiv ℝ f x) x :=
    ((hfa x hx).differentiableAt hn0).hasFDerivAt
  have hpW : p ∈ interior W := mem_interior_iff_mem_nhds.2 hW
  have hfp : HasFDerivAt f (A : E →L[ℝ] E) p := hA ▸ hfd p hpW
  -- the inverse function theorem, then restriction to the points with invertible derivative
  let e₀ := (hfa p hpW).toOpenPartialHomeomorph f hfp hn0
  have hT : IsOpen (interior W ∩ fderiv ℝ f ⁻¹' {T | T.IsInvertible}) :=
    ((hf.mono interior_subset).continuousOn_fderiv_of_isOpen isOpen_interior
      hn1).isOpen_inter_preimage isOpen_interior
      ContinuousLinearMap.isOpen_setOfPred_isInvertible
  let e := e₀.restrOpen _ hT
  have hpe : p ∈ e.source :=
    ⟨(hfa p hpW).mem_toOpenPartialHomeomorph_source hfp hn0, hpW, A, hA.symm⟩
  refine ⟨e, rfl, hpe, fun y hy ↦ ?_, ?_⟩
  · obtain ⟨-, hxW, M, hM⟩ := e.map_target hy
    refine (e.contDiffAt_symm hy (f₀' := M) ?_ (hfa _ hxW)).contDiffWithinAt
    rw [hM]
    exact hfd _ hxW
  · exact ((hfa p hpW).hasStrictFDerivAt' hfp hn0).to_localInverse.hasFDerivAt

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
  obtain ⟨A, hA⟩ := hinv
  obtain ⟨e, he, hpe, hes, hed⟩ := exists_openPartialHomeomorph_contDiffOn_symm hn hW hf hA.symm
  -- the local inverse `e⁻¹` fixes `p`, with derivative `A⁻¹` there
  have hep : e p = p := by rw [he, hfix]
  have hpt : p ∈ e.target := hep ▸ e.map_source hpe
  have hgp : e.symm p = p := by simpa [hep] using e.left_inv hpe
  have hgd : fderiv ℝ e.symm p = (A.symm : E →L[ℝ] E) := by
    rw [hfix] at hed
    exact hed.fderiv
  have hst : (fderiv ℝ e.symm p).stableSubspace = (fderiv ℝ f p).unstableSubspace := by
    rw [hgd, ContinuousLinearMap.stableSubspace_symm, hA]
  have hun : (fderiv ℝ e.symm p).unstableSubspace = (fderiv ℝ f p).stableSubspace := by
    rw [hgd, ContinuousLinearMap.unstableSubspace_symm, hA]
  have hsplit := ContinuousLinearMap.isCompl_stableSubspace_unstableSubspace hyp
  -- the local stable manifold theorem for `f` and for `e⁻¹`
  obtain ⟨δ₁, hδ₁, hs, hsC, hs0, hsd, hsU⟩ :=
    exists_localStableSet_eq_graph_of_isCompl hn hW hf hfix hsplit
  obtain ⟨δ₂, hδ₂, hu, huC, hu0, hud, huU⟩ :=
    exists_localStableSet_eq_graph_of_isCompl hn (e.open_target.mem_nhds hpt) hes hgp
      (by rw [hst, hun]; exact hsplit.symm)
  -- one neighborhood for both
  set U := ball p (min δ₁ δ₂) ∩ e.source ∩ e.target
  have hUo : IsOpen U := (isOpen_ball.inter e.open_source).inter e.open_target
  have hUn : U ∈ 𝓝 p := hUo.mem_nhds ⟨⟨mem_ball_self (lt_min hδ₁ hδ₂), hpe⟩, hpt⟩
  refine ⟨U, hUn, hUo, ?_, ?_⟩
  · obtain ⟨Vs, hVs, heq⟩ :=
      hsU U hUn fun x hx ↦ ball_subset_ball (min_le_left _ _) hx.1.1
    exact ⟨Vs, hVs, hs, hsC.contDiffOn, hs0, hsd, heq⟩
  · obtain ⟨Vu, hVu, heq⟩ :=
      huU U hUn fun x hx ↦ ball_subset_ball (min_le_right _ _) hx.1.1
    have hloc : localUnstableSet f p U = localStableSet e.symm p U := by
      rw [localUnstableSet_congr (g := e) fun x _ ↦ by rw [he]]
      exact (localStableSet_symm_eq_localUnstableSet e fun x (hx : x ∈ U) ↦ ⟨hx.1.2, hx.2⟩).1.symm
    rw [hloc]
    exact exists_graph_ofEq hst hun hVu huC.contDiffOn hu0 hud heq

end Function
