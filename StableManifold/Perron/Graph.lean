/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import StableManifold.Perron.Operator
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# The stable manifold of a small Lipschitz perturbation of a hyperbolic linear map

Let `S` be a hyperbolic splitting of `A` on a real Banach space `E` (projection `P`, constants
`C`, `λ`), and `F x = A x + φ x` a **globally** small Lipschitz perturbation: `φ 0 = 0` and `φ` is
`L`-Lipschitz with `L * S.bound ≤ 1 / 2` (`StableManifold.Perturbation`). Perron's method:

* `Perturbation.perronMap ξ x = stableOrbit ξ + perronOp (superpose φ x)` is a `1/2`-contraction
  of the Banach space `ℕ →ᵇ E` of bounded sequences (`contractingWith_perronMap`); its fixed
  points are the bounded `F`-orbits with stable component `P ξ` at time `0`
  (`Perron.Operator`);
* `Perturbation.orbitSeq ξ`: the fixed point, the unique bounded `F`-orbit with
  `P (orbitSeq ξ 0) = P ξ`; it depends Lipschitz-continuously on `ξ` (`dist_orbitSeq_le`) and decays
  geometrically, `‖orbitSeq ξ n‖ ≤ 2 C θⁿ ‖P ξ‖` with `θ = S.decayRate`
  (`norm_orbitSeq_apply_le`);
* `Perturbation.graph ξ = (1 - P) (orbitSeq ξ 0)`: a Lipschitz map, constant along the unstable
  directions (`graph_proj`), with values in the unstable subspace (`proj_graph`) and `graph 0 = 0`.

**The global stable manifold** (`bddOrbit_iff`): the `F`-orbit of `x` is bounded if and only if
`(1 - P) x = graph x`, that is `x = P x + graph (P x)` lies on the graph of `graph` over the stable
subspace; such orbits tend to `0` geometrically (`norm_iterate_le`). If `φ` has derivative `0` at
`0`, the graph is tangent to the stable subspace: `graph` has derivative `0` at `0`
(`hasFDerivAt_graph_zero`).

## Proofs (plan)

Size: 450–700 lines.

* `contractingWith_perronMap`: `superpose φ` is `L`-Lipschitz (`lipschitzWith_superpose`) and
  `‖perronOp‖ ≤ S.bound` (`norm_perronOp_le`), so `perronMap ξ` is `L * S.bound ≤ 1/2`-Lipschitz
  (`LipschitzWith.const_add`, `ContinuousLinearMap.lipschitz`, `LipschitzWith.comp`,
  `LipschitzWith.weaken`).
* `orbitSeq_succ`, `proj_orbitSeq_apply_zero`: rewrite the fixed point equation and use
  `stableOrbit_add_perronOp_succ`, `proj_stableOrbit_add_perronOp_zero` with
  `superpose_apply_of_lipschitzWith`.
* `eq_orbitSeq_of_forall_succ`: `eq_stableOrbit_add_perronOp` makes `x` a fixed point of
  `perronMap (x 0)`; `ContractingWith.fixedPoint_unique`.
* `orbitSeq_proj`: `perronMap (P ξ) = perronMap ξ` (`stableOrbit_proj`). `orbitSeq_zero`: `0` is a
  fixed point of `perronMap 0` (`superpose_zero`).
* `dist_orbitSeq_le`: `ContractingWith.fixedPoint_lipschitz_in_map`, with
  `dist (perronMap ξ x) (perronMap η x) = ‖stableOrbit (P ξ - P η)‖ ≤ C ‖P ξ - P η‖`
  (`norm_pow_apply_proj_le`, `BoundedContinuousFunction.norm_le`).
* `norm_orbitSeq_apply_le`: the set `K = {x | ∀ n, ‖x n‖ ≤ M θⁿ}`, `M = 2 C ‖P ξ‖`, is closed
  (`isClosed_iInter`, `isClosed_le`, continuity of `BoundedContinuousFunction.evalCLM`), contains
  `0`, and `perronMap ξ` maps it into itself: `‖Aⁿ P ξ‖ ≤ C θⁿ ‖P ξ‖`
  (`norm_pow_apply_proj_le`, `λ ≤ θ`), `‖φ (x n)‖ ≤ L M θⁿ`, and
  `norm_perronOp_apply_le_of_le` gives `S.bound * L * M θⁿ ≤ M θⁿ / 2`. The iterates of `0` stay
  in `K` and tend to the fixed point (`ContractingWith.tendsto_iterate_fixedPoint`,
  `IsClosed.mem_of_tendsto`).
* `graph_proj`, `proj_graph`, `graph_zero`, `orbitSeq_apply_zero`: `orbitSeq_proj`,
  `(1 - P) P = 0`, `P (1 - P) = 0`, `proj_orbitSeq_apply_zero`.
* `lipschitzWith_graph`: `‖1 - P‖ ≤ C` (`norm_one_sub_proj_le`), `dist_orbitSeq_le`, `‖P‖ ≤ C`,
  and `‖x 0‖ ≤ ‖x‖`.
* `orbitSeq_apply_eq_iterate`: `orbitSeq x 0 = P x + graph x = x` (`orbitSeq_apply_zero`), then
  induction with `orbitSeq_succ` (`Function.iterate_succ_apply'`).
* `bddOrbit_iff`: if the orbit is bounded, it is a bounded sequence `z`
  (`BoundedContinuousFunction.ofNormedAddCommGroupDiscrete`) with `z (n + 1) = F (z n)`, so
  `z = orbitSeq x` (`eq_orbitSeq_of_forall_succ`) and
  `(1 - P) x = (1 - P) (orbitSeq x 0) = graph x`; conversely `orbitSeq_apply_eq_iterate` and
  `BoundedContinuousFunction.norm_coe_le_norm`.
* `norm_iterate_le`, `tendsto_iterate`: `orbitSeq_apply_eq_iterate`, `norm_orbitSeq_apply_le`,
  `tendsto_pow_atTop_nhds_zero_of_lt_one`, `squeeze_zero_norm`.
* `hasFDerivAt_graph_zero`: `graph ξ = -∑_j B^(j+1) φ (orbitSeq ξ j)` (`orbitSeq_apply_zero`,
  `perronOp_apply_zero`, `one_sub_proj_mul_unstableInv`). Given `ε > 0`, `‖φ y‖ ≤ ε ‖y‖` for
  `‖y‖ ≤ δ` (`HasFDerivAt.isLittleO`, `φ 0 = 0`); for `‖ξ‖ ≤ δ / (2 C²)`, `‖orbitSeq ξ j‖ ≤ δ`,
  so `‖graph ξ‖ ≤ ∑_j C λ^(j+1) ε 2 C² ‖ξ‖ ≤ (2 C³ / (1 - λ)) ε ‖ξ‖`. So `graph ξ = o(ξ)`, which
  with `graph 0 = 0` is `HasFDerivAt graph 0 0` (`hasFDerivAt_iff_isLittleO_nhds_zero`).
-/

@[expose] public section

open Filter Topology
open scoped NNReal BoundedContinuousFunction

namespace StableManifold

open BoundedContinuousFunction ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {A : E →L[ℝ] E}

/-- A **globally small Lipschitz perturbation** `x ↦ A x + φ x` of a linear map `A` with a
hyperbolic splitting `S`: `φ 0 = 0` and `φ` is `L`-Lipschitz with `L * S.bound ≤ 1 / 2`. -/
structure Perturbation (S : A.HyperbolicSplitting) where
  /-- The nonlinear part. -/
  φ : E → E
  /-- The Lipschitz constant `L` of the nonlinear part. -/
  lip : ℝ≥0
  lipschitzWith : LipschitzWith lip φ
  map_zero : φ 0 = 0
  lip_mul_bound_le : (lip : ℝ) * S.bound ≤ 1 / 2

namespace Perturbation

variable {S : A.HyperbolicSplitting} (F : Perturbation S)

/-- The perturbed map `x ↦ A x + φ x`. -/
def map (x : E) : E := A x + F.φ x

theorem map_apply (x : E) : F.map x = A x + F.φ x :=
  rfl

theorem map_zero' : F.map 0 = 0 := by
  simp [map, F.map_zero]

variable [CompleteSpace E]

/-- The **Lyapunov–Perron map** `x ↦ stableOrbit ξ + perronOp (φ ∘ x)` on bounded sequences: its
fixed points are the bounded `F`-orbits with stable component `P ξ` at time `0`. -/
noncomputable def perronMap (ξ : E) (x : ℕ →ᵇ E) : ℕ →ᵇ E :=
  S.stableOrbit ξ + S.perronOp (superpose F.φ x)

theorem perronMap_apply (ξ : E) (x : ℕ →ᵇ E) :
    F.perronMap ξ x = S.stableOrbit ξ + S.perronOp (superpose F.φ x) :=
  rfl

/-- The Lyapunov–Perron map is a `1/2`-contraction.

Proof: it is `L * S.bound`-Lipschitz (`lipschitzWith_superpose`, `norm_perronOp_le`). -/
theorem contractingWith_perronMap (ξ : E) : ContractingWith (1 / 2) (F.perronMap ξ) := by
  sorry

/-- The **bounded orbit** through `ξ`: the fixed point of `perronMap ξ`, the unique bounded
`F`-orbit with stable component `P ξ` at time `0`. -/
noncomputable def orbitSeq (ξ : E) : ℕ →ᵇ E :=
  ContractingWith.fixedPoint (F.perronMap ξ) (F.contractingWith_perronMap ξ)

theorem perronMap_orbitSeq (ξ : E) : F.perronMap ξ (F.orbitSeq ξ) = F.orbitSeq ξ :=
  ContractingWith.fixedPoint_isFixedPt (F.contractingWith_perronMap ξ)

theorem eq_orbitSeq_of_perronMap_eq {ξ : E} {x : ℕ →ᵇ E} (hx : F.perronMap ξ x = x) :
    x = F.orbitSeq ξ :=
  ContractingWith.fixedPoint_unique (F.contractingWith_perronMap ξ) hx

/-- `orbitSeq ξ` is an `F`-orbit. -/
theorem orbitSeq_succ (ξ : E) (n : ℕ) : F.orbitSeq ξ (n + 1) = F.map (F.orbitSeq ξ n) := by
  sorry

/-- `orbitSeq ξ` has stable component `P ξ` at time `0`. -/
theorem proj_orbitSeq_apply_zero (ξ : E) : S.proj (F.orbitSeq ξ 0) = S.proj ξ := by
  sorry

/-- **Uniqueness**: a bounded `F`-orbit `x` is `orbitSeq (x 0)`.

Proof: by `eq_stableOrbit_add_perronOp`, `x` is a fixed point of `perronMap (x 0)`. -/
theorem eq_orbitSeq_of_forall_succ {x : ℕ →ᵇ E} (hx : ∀ n, x (n + 1) = F.map (x n)) :
    x = F.orbitSeq (x 0) := by
  sorry

theorem orbitSeq_proj (ξ : E) : F.orbitSeq (S.proj ξ) = F.orbitSeq ξ := by
  sorry

theorem orbitSeq_zero : F.orbitSeq 0 = 0 := by
  sorry

/-- `orbitSeq` is Lipschitz in the stable component.

Proof: `ContractingWith.fixedPoint_lipschitz_in_map`, the two Lyapunov–Perron maps differing by
`stableOrbit (ξ - η)`, of norm `≤ C ‖P ξ - P η‖`. -/
theorem dist_orbitSeq_le (ξ η : E) :
    dist (F.orbitSeq ξ) (F.orbitSeq η) ≤ 2 * S.const * ‖S.proj ξ - S.proj η‖ := by
  sorry

/-- **Geometric decay** of the bounded orbits: `‖orbitSeq ξ n‖ ≤ 2 C θⁿ ‖P ξ‖`,
`θ = S.decayRate`.

Proof: `perronMap ξ` maps the closed set `{x | ∀ n, ‖x n‖ ≤ 2 C ‖P ξ‖ θⁿ}` into itself
(`norm_perronOp_apply_le_of_le`), so its fixed point lies there. -/
theorem norm_orbitSeq_apply_le (ξ : E) (n : ℕ) :
    ‖F.orbitSeq ξ n‖ ≤ 2 * S.const * S.decayRate ^ n * ‖S.proj ξ‖ := by
  sorry

/-- The map whose graph over the stable subspace is the **global stable manifold**:
`graph ξ = (1 - P) (orbitSeq ξ 0)`, the unstable component at time `0` of the bounded orbit with
stable component `P ξ`. -/
noncomputable def graph (ξ : E) : E :=
  (1 - S.proj) (F.orbitSeq ξ 0)

theorem graph_proj (ξ : E) : F.graph (S.proj ξ) = F.graph ξ := by
  sorry

theorem proj_graph (ξ : E) : S.proj (F.graph ξ) = 0 := by
  sorry

theorem graph_zero : F.graph 0 = 0 := by
  sorry

/-- The bounded orbit through `ξ` starts at `P ξ + graph ξ`. -/
theorem orbitSeq_apply_zero (ξ : E) : F.orbitSeq ξ 0 = S.proj ξ + F.graph ξ := by
  sorry

/-- `graph` is Lipschitz, with constant `2 C³`. -/
theorem lipschitzWith_graph : LipschitzWith (2 * S.const ^ 3).toNNReal F.graph := by
  sorry

/-- On the graph, the bounded orbit is the forward `F`-orbit. -/
theorem orbitSeq_apply_eq_iterate {x : E} (hx : (1 - S.proj) x = F.graph x) (n : ℕ) :
    F.orbitSeq x n = F.map^[n] x := by
  sorry

/-- **The global stable manifold**: the forward `F`-orbit of `x` is bounded if and only if
`(1 - P) x = graph x`, that is `x = P x + graph (P x)`.

Proof: a bounded orbit is `orbitSeq x` (`eq_orbitSeq_of_forall_succ`), whose unstable component at
`0` is `graph x`; conversely `orbitSeq_apply_eq_iterate`. -/
theorem bddOrbit_iff (x : E) :
    (∃ M, ∀ n, ‖F.map^[n] x‖ ≤ M) ↔ (1 - S.proj) x = F.graph x := by
  sorry

/-- On the graph, the forward orbits decay geometrically: `‖Fⁿ x‖ ≤ 2 C θⁿ ‖P x‖`. -/
theorem norm_iterate_le {x : E} (hx : (1 - S.proj) x = F.graph x) (n : ℕ) :
    ‖F.map^[n] x‖ ≤ 2 * S.const * S.decayRate ^ n * ‖S.proj x‖ := by
  sorry

/-- On the graph, the forward orbits tend to `0`. -/
theorem tendsto_iterate {x : E} (hx : (1 - S.proj) x = F.graph x) :
    Tendsto (fun n ↦ F.map^[n] x) atTop (𝓝 0) := by
  sorry

/-- **Tangency**: if `φ` has derivative `0` at `0`, so has `graph`; the stable manifold is tangent
to the stable subspace at `0`.

Proof: `graph ξ = -∑_j B^(j+1) φ (orbitSeq ξ j)`, with `‖orbitSeq ξ j‖ ≤ 2 C² ‖ξ‖` and
`‖φ y‖ ≤ ε ‖y‖` near `0`, so `‖graph ξ‖ ≤ (2 C³ / (1 - λ)) ε ‖ξ‖` near `0`. -/
theorem hasFDerivAt_graph_zero (hφ : HasFDerivAt F.φ (0 : E →L[ℝ] E) 0) :
    HasFDerivAt F.graph (0 : E →L[ℝ] E) 0 := by
  sorry

end Perturbation

end StableManifold
