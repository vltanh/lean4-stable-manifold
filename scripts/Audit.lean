module

public meta import Lean.Elab.Command
public import Mathlib.Analysis.InnerProductSpace.PiL2
-- One `import all` line per module of the library, so that proofs are visible to the axiom
-- traversal (the module system hides them from a plain `import`). Generate the lines with
--   find StableManifold -name '*.lean' | sort | sed 's/\.lean$//; s#/#.#g; s/^/import all /'
import all StableManifold.Defs
import all StableManifold.Linear.HyperbolicSplitting
import all StableManifold.Linear.Spectral
import all StableManifold.Linear.Splitting
import all StableManifold.Linear.Subspaces
import all StableManifold.Local.Cutoff
import all StableManifold.LocalSets
import all StableManifold.Local.StableSet
import all StableManifold.Perron.Graph
import all StableManifold.Perron.Operator
import all StableManifold.Perron.Smooth
import all StableManifold.Sequence.SuperposeContDiff
import all StableManifold.Sequence.Superpose
import all StableManifold.Theorem
-- The Challenge's theorems, as `StableManifoldSolution.lean` restates and proves them.
import all StableManifoldSolution

/-!
# Axiom audit

Run with `lake env lean scripts/Audit.lean` after `lake build`.

Prints the axioms on which the main theorems depend (`#print axioms`), then checks that they, the
theorems of `StableManifoldChallenge.lean` as `StableManifoldSolution.lean` proves them, and every
declaration of the library, including private and auxiliary ones, depend only on Lean's standard
axioms `propext`, `Classical.choice` and `Quot.sound`. A `sorry` would show up as the axiom
`sorryAx`. The run fails otherwise.

Finally, it checks that the hypotheses of the main theorem can be met, and that the theorems
apply in a few concrete forms.
-/

open Lean Elab Command

namespace Audit

/-- The main theorems of the library, and the Challenge's theorems as the Solution proves them. -/
meta def mainResults : List Name :=
  [``Function.exists_nhds_localStableSet_localUnstableSet_eq_graph,
   ``Function.exists_localStableSet_localUnstableSet_eq_graph,
   ``Function.exists_nhds_localStableSet_localUnstableSet_eq_setOf,
   ``Function.exists_localStableSet_eq_graph_of_isCompl,
   ``Function.exists_localStableSet_eq_setOf_forall_iterate_mem,
   ``Function.setOf_forall_iterate_symm_mem_eq,
   ``Function.exists_openPartialHomeomorph_contDiffOn_symm,
   ``Function.localStableSet_symm_eq_localUnstableSet,
   ``ContinuousLinearMap.isCompl_stableSubspace_unstableSubspace,
   ``ContinuousLinearMap.disjoint_stableSubspace_unstableSubspace,
   ``ContinuousLinearMap.codisjoint_stableSubspace_unstableSubspace,
   ``ContinuousLinearMap.exists_stableSubspace_unstableSubspace_eq_ker_aeval,
   ``ContinuousLinearMap.stableSubspace_symm,
   ``ContinuousLinearMap.unstableSubspace_symm,
   ``ContinuousLinearMap.nonempty_hyperbolicSplitting,
   ``ContinuousLinearMap.exists_norm_pow_lt_one,
   ``ContinuousLinearMap.exists_norm_pow_le_mul_pow_of_tendsto,
   ``Polynomial.exists_isCoprime_roots_lt_one_one_lt,
   ``StableManifold.contDiff_superpose,
   ``StableManifold.exists_contDiff_lipschitzWith_eqOn_ball,
   ``StableManifold.Perturbation.contractingWith_perronMap,
   ``StableManifold.Perturbation.bddOrbit_iff,
   ``StableManifold.Perturbation.norm_iterate_le,
   ``StableManifold.Perturbation.hasFDerivAt_graph_zero,
   ``StableManifold.Perturbation.contDiff_graph,
   ``StableManifold.Perturbation.exists_localStableSet_map_eq_image,
   ``StableManifoldChallenge.stable_manifold_forall_nhds,
   ``StableManifoldChallenge.stable_manifold,
   ``StableManifoldChallenge.hyperbolic_splitting,
   ``StableManifoldChallenge.stableSubspace_symm,
   ``StableManifoldChallenge.localStableSet_symm]

/-- Lean's standard axioms. -/
meta def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Whether `m` is a module of the library. -/
meta def isLibraryModule (m : Name) : Bool := (`StableManifold).isPrefixOf m

/-- The constants declared in the library. -/
meta def libraryConstants (env : Environment) : Array Name := Id.run do
  let mut out : Array Name := #[]
  for m in env.header.moduleNames, d in env.header.moduleData do
    if isLibraryModule m then
      out := out ++ d.constNames
  return out

elab "#audit" : command => do
  let env ← getEnv
  let mut bad : Array Name := #[]
  let mut rows : Array String := #[]
  for n in mainResults do
    let axs ← liftCoreM <| collectAxioms n
    if axs.any (!standardAxioms.contains ·) then bad := bad.push n
    rows := rows.push s!"{n}: {axs.toList}"
  let library := libraryConstants env
  for c in library do
    let axs ← liftCoreM <| collectAxioms c
    if axs.any (!standardAxioms.contains ·) then bad := bad.push c
  logInfo ("\n".intercalate rows.toList ++
    s!"\n\nChecked {library.size} declarations of the library: " ++
    (if bad.isEmpty then "all use only the standard axioms." else "see the error."))
  unless bad.isEmpty do
    throwError m!"non-standard axioms used by: {bad}"

end Audit

#print axioms Function.exists_nhds_localStableSet_localUnstableSet_eq_graph
#print axioms Function.exists_localStableSet_localUnstableSet_eq_graph
#print axioms Function.exists_localStableSet_eq_graph_of_isCompl
#print axioms ContinuousLinearMap.isCompl_stableSubspace_unstableSubspace
#print axioms StableManifold.Perturbation.contDiff_graph

#audit

/-! ## The hypotheses can be met -/

/-- Every hypothesis of the stable manifold theorem holds for `f x = -2 x` at its fixed point `0`,
with `n = ∞` and `W = E`: the derivative `A = -2` is invertible, and hyperbolic since its
characteristic polynomial is `(X + 2) ^ d`. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    let f : E → E := fun x ↦ (-2 : ℝ) • x
    (1 : ℕ∞) ≤ ⊤ ∧ Set.univ ∈ nhds (0 : E) ∧ ContDiffOn ℝ (⊤ : ℕ∞) f Set.univ ∧ f 0 = 0 ∧
      (fderiv ℝ f 0).IsInvertible ∧ (fderiv ℝ f 0).IsHyperbolic := by
  intro f
  have hd : fderiv ℝ f 0 = (-2 : ℝ) • ContinuousLinearMap.id ℝ E :=
    ((-2 : ℝ) • ContinuousLinearMap.id ℝ E).fderiv
  refine ⟨le_top, Filter.univ_mem, (contDiff_const_smul _).contDiffOn, by simp [f], ?_, ?_⟩
  · rw [hd]
    exact ⟨ContinuousLinearEquiv.smulLeft (Units.mk0 (-2 : ℝ) (by norm_num)), by ext; simp⟩
  · rw [hd]
    intro μ hμ
    have h : (((-2 : ℝ) • ContinuousLinearMap.id ℝ E : E →L[ℝ] E) : E →ₗ[ℝ] E) =
        0 - (2 : ℝ) • 1 := by
      ext x; simp [neg_smul]
    rw [h, LinearMap.charpoly_sub_smul, LinearMap.charpoly_zero] at hμ
    simp only [Polynomial.X_pow_comp, map_pow, map_add, Polynomial.aeval_X,
      Polynomial.aeval_C] at hμ
    have : μ = -2 := by
      have := (pow_eq_zero_iff'.1 hμ).1
      simp only [Complex.coe_algebraMap, Complex.ofReal_ofNat] at this
      linear_combination this
    simp [this]

/-! ## The statements in concrete forms -/

open Filter Topology in
/-- For a smooth map of `ℝᵈ`, the local stable set is the graph of a smooth map. -/
example (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (p : EuclideanSpace ℝ (Fin d)) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfix : f p = p)
    (hinv : (fderiv ℝ f p).IsInvertible) (hyp : (fderiv ℝ f p).IsHyperbolic) :
    ∃ U ∈ 𝓝 p, ∃ Vs ∈ 𝓝 (0 : (fderiv ℝ f p).stableSubspace),
      ∃ hs : (fderiv ℝ f p).stableSubspace → (fderiv ℝ f p).unstableSubspace,
        ContDiffOn ℝ (⊤ : ℕ∞) hs Vs ∧
          Function.localStableSet f p U = (fun x ↦ p + ↑x + ↑(hs x)) '' Vs := by
  obtain ⟨U, hU, -, ⟨Vs, hVs, hs, hsC, -, -, heq⟩, -⟩ :=
    Function.exists_localStableSet_localUnstableSet_eq_graph le_top univ_mem hf.contDiffOn hfix
      hinv hyp
  exact ⟨U, hU, Vs, hVs, hs, hsC, heq⟩

open Filter Topology Metric in
/-- One pair of graph maps serves for every ball around `p` of small radius: the usual "for every
small `ε`" form of the theorem. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → E} {p : E} {W : Set E} {n : ℕ∞} (hn : 1 ≤ n) (hW : W ∈ 𝓝 p)
    (hf : ContDiffOn ℝ n f W) (hfix : f p = p) (hinv : (fderiv ℝ f p).IsInvertible)
    (hyp : (fderiv ℝ f p).IsHyperbolic) :
    ∃ hs : (fderiv ℝ f p).stableSubspace → (fderiv ℝ f p).unstableSubspace,
      ∃ hu : (fderiv ℝ f p).unstableSubspace → (fderiv ℝ f p).stableSubspace,
      ∃ ε₀ > 0, ∀ ε ∈ Set.Ioc 0 ε₀,
        (∃ Vs ∈ 𝓝 (0 : (fderiv ℝ f p).stableSubspace),
          Function.localStableSet f p (ball p ε) = (fun x ↦ p + ↑x + ↑(hs x)) '' Vs) ∧
        (∃ Vu ∈ 𝓝 (0 : (fderiv ℝ f p).unstableSubspace),
          Function.localUnstableSet f p (ball p ε) = (fun y ↦ p + ↑y + ↑(hu y)) '' Vu) := by
  obtain ⟨N, hN, hs, -, -, -, hu, -, -, -, hNU⟩ :=
    Function.exists_nhds_localStableSet_localUnstableSet_eq_graph hn hW hf hfix hinv hyp
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.mem_nhds_iff.1 hN
  exact ⟨hs, hu, ε₀, hε₀, fun ε hε ↦ hNU _ (ball_mem_nhds p hε.1)
    ((ball_subset_ball hε.2).trans hball)⟩

/-- For a hyperbolic linear map, the dimensions of the stable and unstable subspaces add up to the
dimension of the space. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A : E →L[ℝ] E} (hA : A.IsHyperbolic) :
    Module.finrank ℝ A.stableSubspace + Module.finrank ℝ A.unstableSubspace =
      Module.finrank ℝ E :=
  Submodule.finrank_add_eq_of_isCompl
    (ContinuousLinearMap.isCompl_stableSubspace_unstableSubspace hA)

open Filter Topology Metric in
/-- The stable side needs no invertibility: for a `C¹` map with hyperbolic derivative at a fixed
point, one map `hₛ` describes the local stable set of every neighborhood inside a small ball. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → E} {p : E} {W : Set E} (hW : W ∈ 𝓝 p) (hf : ContDiffOn ℝ (1 : ℕ∞) f W)
    (hfix : f p = p) (hyp : (fderiv ℝ f p).IsHyperbolic) :
    ∃ δ > 0, ∃ hs : (fderiv ℝ f p).stableSubspace → (fderiv ℝ f p).unstableSubspace,
      ContDiff ℝ (1 : ℕ∞) hs ∧ hs 0 = 0 ∧ fderiv ℝ hs 0 = 0 ∧
      ∀ U ∈ 𝓝 p, U ⊆ ball p δ →
        ∃ Vs ∈ 𝓝 (0 : (fderiv ℝ f p).stableSubspace),
          Function.localStableSet f p U = (fun x ↦ p + ↑x + ↑(hs x)) '' Vs :=
  Function.exists_localStableSet_eq_graph_of_isCompl le_rfl hW hf hfix
    (ContinuousLinearMap.isCompl_stableSubspace_unstableSubspace hyp)
