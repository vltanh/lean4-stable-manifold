/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.OpenPartialHomeomorph.Defs
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Local stable and unstable sets of a fixed point

For a map `f : X → X` of a topological space, a point `p` and a set `U`:

* `Function.localStableSet f p U`: the points whose forward orbit stays in `U` and tends to `p`
  (the local stable set of `f|_U`);
* `Function.globalStableSet f p`: the points whose forward orbit tends to `p`;
* `Function.localUnstableSet f p U`: the points having a backward orbit (`f (y (n + 1)) = y n`) in
  `U` that tends to `p` (the local stable set of `f⁻¹|_U` when `f` is invertible; the definition
  does not need an inverse).

Elementary facts:

* `Function.eventually_iterate_mem_localStableSet`, `Function.eventually_mem_localUnstableSet`:
  an orbit tending to `p` eventually lies in the local stable set of every neighborhood of `p`,
  and a backward orbit tending to `p` eventually lies in the local unstable set;
* `Function.localStableSet_symm_eq_localUnstableSet`: unstable for `e` is stable for `e⁻¹`;
* `Function.localStableSet_congr`, `Function.localUnstableSet_congr`: the local sets of `f|_U`
  depend only on `f|_U`;
* `Function.localStableSet_conj`, `Function.localUnstableSet_conj`: conjugating `f` by a
  homeomorphism `e` carries the local sets along `e` (used with a translation, to move the fixed
  point to `0`).

## Proofs (plan)

All proofs are short manipulations of the definitions; about 150 lines in all.

* `eventually_iterate_mem_localStableSet`: `fⁿ x ∈ U` for `n ≥ N`; then
  `f^[k] (f^[n] x) = f^[k + n] x ∈ U` (`Function.iterate_add_apply`) and tends to `p`
  (`Filter.tendsto_add_atTop_iff_nat`).
* `eventually_mem_localUnstableSet`: `y n ∈ U` for `n ≥ N`; use the backward orbit
  `k ↦ y (n + k)`.
* `localStableSet_symm_eq_localUnstableSet`: if `y n = e.symm^[n] x ∈ U ⊆ e.target`, then
  `e (y (n + 1)) = e (e.symm (y n)) = y n` (`OpenPartialHomeomorph.right_inv`); conversely, if
  `e (y (n + 1)) = y n` with `y (n + 1) ∈ U ⊆ e.source`, then `e.symm (y n) = y (n + 1)`
  (`OpenPartialHomeomorph.left_inv`), so `y n = e.symm^[n] x` by induction.
* `localStableSet_congr`: if the `f`-orbit of `x` stays in `U`, then `f^[n] x = g^[n] x` by
  induction on `n` (`Function.iterate_succ_apply'`); symmetrically for `g`.
  `localUnstableSet_congr`: `f (y (n + 1)) = g (y (n + 1))` since `y (n + 1) ∈ U`.
* `localStableSet_conj`: `(e ∘ f ∘ e.symm)^[n] = e ∘ f^[n] ∘ e.symm`
  (`Function.Semiconj.iterate_right`, or induction), `e y ∈ e '' U ↔ y ∈ U`, and `e`, `e.symm`
  are continuous. `localUnstableSet_conj`: map backward orbits by `e` and by `e.symm`.
-/

@[expose] public section

open Filter Topology Set

namespace Function

variable {X : Type*} [TopologicalSpace X]

/-- The **local stable set** of `f|_U` at `p`: the points `x` whose forward orbit `fⁿ(x)` stays in
`U` and tends to `p`. (For the iterates of `f|_U` to be defined the orbit must stay in `U`.) -/
def localStableSet (f : X → X) (p : X) (U : Set X) : Set X :=
  {x | (∀ n : ℕ, f^[n] x ∈ U) ∧ Tendsto (fun n : ℕ ↦ f^[n] x) atTop (𝓝 p)}

/-- The **global stable set** of `f` at `p`: the points whose forward orbit tends to `p`. -/
def globalStableSet (f : X → X) (p : X) : Set X :=
  {x | Tendsto (fun n : ℕ ↦ f^[n] x) atTop (𝓝 p)}

/-- The **local unstable set** of `f|_U` at `p`: the points `x` having a backward orbit `y`
(`y 0 = x`, `f (y (n + 1)) = y n`) in `U` that tends to `p`. For an `f` invertible on `U` it is the
local stable set of `f⁻¹|_U` (`Function.localStableSet_symm_eq_localUnstableSet`). -/
def localUnstableSet (f : X → X) (p : X) (U : Set X) : Set X :=
  {x | ∃ y : ℕ → X, y 0 = x ∧ (∀ n, y n ∈ U ∧ f (y (n + 1)) = y n) ∧ Tendsto y atTop (𝓝 p)}

/-- A point of the local stable set lies in `U`. -/
theorem mem_of_mem_localStableSet {f : X → X} {p : X} {U : Set X} {x : X}
    (h : x ∈ localStableSet f p U) : x ∈ U := by
  simpa using h.1 0

/-- A point of the local unstable set lies in `U`. -/
theorem mem_of_mem_localUnstableSet {f : X → X} {p : X} {U : Set X} {x : X}
    (h : x ∈ localUnstableSet f p U) : x ∈ U := by
  obtain ⟨y, rfl, hy, -⟩ := h
  exact (hy 0).1

/-- The local stable set lies in the global stable set. -/
theorem localStableSet_subset_globalStableSet (f : X → X) (p : X) (U : Set X) :
    localStableSet f p U ⊆ globalStableSet f p :=
  fun _ hx ↦ hx.2

/-- **An orbit tending to `p` eventually lies in the local stable set** of any neighborhood `U`
of `p`: the tail of the orbit stays in `U`.

Proof: `fⁿ(x) ∈ U` for `n ≥ N`; then `f^[k] (f^[n] x) = f^[k + n] x ∈ U` and tends to `p`. -/
theorem eventually_iterate_mem_localStableSet {f : X → X} {p : X} {U : Set X} (hU : U ∈ 𝓝 p)
    {x : X} (hx : Tendsto (fun n : ℕ ↦ f^[n] x) atTop (𝓝 p)) :
    ∀ᶠ n in atTop, f^[n] x ∈ localStableSet f p U := by
  sorry

/-- **A backward orbit tending to `p` eventually lies in the local unstable set** of any
neighborhood `U` of `p`: if `f (y (n + 1)) = y n` for all `n` and `y n → p`, then `y n` lies in
`localUnstableSet f p U` for all large `n` (with the backward orbit `k ↦ y (n + k)`). -/
theorem eventually_mem_localUnstableSet {f : X → X} {p : X} {U : Set X} (hU : U ∈ 𝓝 p)
    {y : ℕ → X} (hy : ∀ n, f (y (n + 1)) = y n) (ht : Tendsto y atTop (𝓝 p)) :
    ∀ᶠ n in atTop, y n ∈ localUnstableSet f p U := by
  sorry

/-- **Unstable for `f` means stable for `f⁻¹`**: for an open partial homeomorphism `e` and a set
`U` inside both its source and its target, the local stable set of `e⁻¹|_U` is the local unstable
set of `e|_U` (a forward `e⁻¹`-orbit in `U` is a backward `e`-orbit, and conversely), and
symmetrically.

Proof: if `y n = e.symm^[n] x ∈ U ⊆ e.target`, then `e (y (n + 1)) = e (e.symm (y n)) = y n`;
conversely, if `e (y (n + 1)) = y n` with `y (n + 1) ∈ U ⊆ e.source`, then
`e.symm (y n) = y (n + 1)`, so `y n = e.symm^[n] x` by induction. -/
theorem localStableSet_symm_eq_localUnstableSet (e : OpenPartialHomeomorph X X) {p : X}
    {U : Set X} (hU : U ⊆ e.source ∩ e.target) :
    localStableSet e.symm p U = localUnstableSet e p U ∧
      localUnstableSet e.symm p U = localStableSet e p U := by
  sorry

/-- The local stable set of `f|_U` depends only on the values of `f` on `U`.

Proof: if the `f`-orbit of `x` stays in `U`, then `f^[n] x = g^[n] x` by induction on `n`, so the
`g`-orbit is the same; symmetrically. -/
theorem localStableSet_congr {f g : X → X} {p : X} {U : Set X} (h : EqOn f g U) :
    localStableSet f p U = localStableSet g p U := by
  sorry

/-- The local unstable set of `f|_U` depends only on the values of `f` on `U`.

Proof: a backward orbit `y` in `U` has `f (y (n + 1)) = g (y (n + 1))` since `y (n + 1) ∈ U`. -/
theorem localUnstableSet_congr {f g : X → X} {p : X} {U : Set X} (h : EqOn f g U) :
    localUnstableSet f p U = localUnstableSet g p U := by
  sorry

/-- **Conjugation** carries local stable sets along: for a homeomorphism `e : X ≃ₜ Y`, the local
stable set of `e ∘ f ∘ e⁻¹` at `e p` in `e '' U` is the image by `e` of the local stable set of `f`
at `p` in `U`.

Proof: `(e ∘ f ∘ e.symm)^[n] = e ∘ f^[n] ∘ e.symm` (by induction on `n`), `e y ∈ e '' U ↔ y ∈ U`,
and `e`, `e.symm` are continuous, so they carry convergent orbits to convergent orbits. -/
theorem localStableSet_conj {Y : Type*} [TopologicalSpace Y] (e : X ≃ₜ Y) (f : X → X) (p : X)
    (U : Set X) :
    localStableSet (e ∘ f ∘ e.symm) (e p) (e '' U) = e '' localStableSet f p U := by
  sorry

/-- **Conjugation** carries local unstable sets along: for a homeomorphism `e : X ≃ₜ Y`, the local
unstable set of `e ∘ f ∘ e⁻¹` at `e p` in `e '' U` is the image by `e` of the local unstable set of
`f` at `p` in `U`.

Proof: a backward `f`-orbit `y` in `U` gives the backward orbit `e ∘ y` in `e '' U`, and a backward
`(e ∘ f ∘ e.symm)`-orbit `z` in `e '' U` gives the backward `f`-orbit `e.symm ∘ z` in `U`;
continuity of `e` and `e.symm` carries the limits. -/
theorem localUnstableSet_conj {Y : Type*} [TopologicalSpace Y] (e : X ≃ₜ Y) (f : X → X) (p : X)
    (U : Set X) :
    localUnstableSet (e ∘ f ∘ e.symm) (e p) (e '' U) = e '' localUnstableSet f p U := by
  sorry

end Function
