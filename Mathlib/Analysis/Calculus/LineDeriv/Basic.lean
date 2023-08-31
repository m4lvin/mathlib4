/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

#align_import analysis.calculus.deriv.basic from "leanprover-community/mathlib"@"3bce8d800a6f2b8f63fe1e588fd76a9ff4adcebe"

/-!
# Line derivatives

We define the derivative of a function `f : E → F`, at a point `x : E` along a vector `v : E`, as
the element `f' : F` such that `f (x + t • v) = f x + t • f' + o (t)` as `t` tends to `0`, if it
exists. It is denoted by `lineDeriv 𝕜 f x v`.

This notion is generally less well behaved than the full Fréchet derivative (for instance, the
composition of functions which are line-differentiable is not line-differentiable in general).
The Fréchet derivative should therefore be favored over this one in general, although the line
derivative may sometimes prove handy.

## Main definition and results

We mimick the definitions and statements for the Fréchet derivative and the one-dimensional
derivative. We define in particular the following objects:

* `LineDifferentiableWithinAt 𝕜 f s x v`
* `LineDifferentiableAt 𝕜 f x v`
* `HasLineDerivWithinAt 𝕜 f f' s x v`
* `HasLineDerivAt 𝕜 f s x v`
* `lineDerivWithin 𝕜 f s x v`
* `lineDeriv 𝕜 f x v`

and develop about them a basic API inspired by the one for the Fréchet derivative.

We depart from the Fréchet derivative in two places, as the dependence of the following predicates
on the direction would make them barely usable:
* We do not define an analogue of the predicate `UniqueDiffOn`;
* We do not define `LineDifferentiableOn` nor `LineDifferentiable`.
-/

noncomputable section

open scoped Topology BigOperators Filter ENNReal

open Filter Asymptotics Set

open ContinuousLinearMap (smulRight smulRight_one_eq_iff)

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section Module
/-!
Results that do not rely on a topological structure on `E`
-/

variable (𝕜)
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]

/-- `f` has the derivative `f'` at the point `x` along the direction `v` in the set `s`.
That is, `f (x + t v) = f x + t • f' + o (t)` when `t` tends to `0` and `x + t v ∈ s`.
Note that this definition is less well behaved that the total Fréchet derivative, which
should generally be favored over this one. -/
def HasLineDerivWithinAt (f : E → F) (f' : F) (s : Set E) (x : E) (v : E) :=
  HasDerivWithinAt (fun t ↦ f (x + t • v)) f' ((fun t ↦ x + t • v) ⁻¹' s) (0 : 𝕜)

/-- `f` has the derivative `f'` at the point `x` along the direction `v`.
That is, `f (x + t v) = f x + t • f' + o (t)` when `t` tends to `0`.
Note that this definition is less well behaved that the total Fréchet derivative, which
should generally be favored over this one. -/
def HasLineDerivAt (f : E → F) (f' : F) (x : E) (v : E) :=
  HasDerivAt (fun t ↦ f (x + t • v)) f' (0 : 𝕜)

/-- `f` is line-differentiable at the point `x` in the direction `v` in the set `s` if there
exists `f'` such that `f (x + t v) = f x + t • f' + o (t)` when `t` tends to `0` and `x + t v ∈ s`.
-/
def LineDifferentiableWithinAt (f : E → F) (s : Set E) (x : E) (v : E) : Prop :=
  DifferentiableWithinAt 𝕜 (fun t ↦ f (x + t • v)) ((fun t ↦ x + t • v) ⁻¹' s) (0 : 𝕜)

/-- `f` is line-differentiable at the point `x` in the direction `v` if there
exists `f'` such that `f (x + t v) = f x + t • f' + o (t)` when `t` tends to `0`. -/
def LineDifferentiableAt (f : E → F) (x : E) (v : E) : Prop :=
  DifferentiableAt 𝕜 (fun t ↦ f (x + t • v)) (0 : 𝕜)

/-- Line derivative of `f` at the point `x` in the direction `v` within the set `s`, if it exists.
Zero otherwise.

If the line derivative exists (i.e., `∃ f', HasLineDerivWithinAt 𝕜 f f' s x v`), then
`f (x + t v) = f x + t lineDerivWithin 𝕜 f s x v + o (t)` when `t` tends to `0` and `x + t v ∈ s`.
-/
def lineDerivWithin (f : E → F) (s : Set E) (x : E) (v : E) : F :=
  derivWithin (fun t ↦ f (x + t • v)) ((fun t ↦ x + t • v) ⁻¹' s) (0 : 𝕜)

/-- Line derivative of `f` at the point `x` in the direction `v`, if it exists.  Zero otherwise.

If the derivative exists (i.e., `∃ f', HasLineDerivAt 𝕜 f f' x v`), then
`f (x + t v) = f x + t lineDerivWithin 𝕜 f x v + o (t)` when `t` tends to `0` and `x + t v ∈ s`.
-/
def lineDeriv (f : E → F) (x : E) (v : E) : F :=
  deriv (fun t ↦ f (x + t • v)) (0 : 𝕜)

variable {𝕜}
variable {f f₁ : E → F} {f' f₀' f₁' : F} {s t : Set E} {x v : E}

lemma HasLineDerivWithinAt.mono (hf : HasLineDerivWithinAt 𝕜 f f' s x v) (hst : t ⊆ s) :
    HasLineDerivWithinAt 𝕜 f f' t x v :=
  HasDerivWithinAt.mono hf (preimage_mono hst)

lemma HasLineDerivAt.hasLineDerivWithinAt (hf : HasLineDerivAt 𝕜 f f' x v) (s : Set E) :
    HasLineDerivWithinAt 𝕜 f f' s x v :=
  HasDerivAt.hasDerivWithinAt hf

lemma HasLineDerivWithinAt.lineDifferentiableWithinAt (hf : HasLineDerivWithinAt 𝕜 f f' s x v) :
    LineDifferentiableWithinAt 𝕜 f s x v :=
  HasDerivWithinAt.differentiableWithinAt hf

theorem HasLineDerivAt.lineDifferentiableAt (hf : HasLineDerivAt 𝕜 f f' x v) :
    LineDifferentiableAt 𝕜 f x v :=
  HasDerivAt.differentiableAt hf

theorem LineDifferentiableWithinAt.hasLineDerivWithinAt (h : LineDifferentiableWithinAt 𝕜 f s x v) :
    HasLineDerivWithinAt 𝕜 f (lineDerivWithin 𝕜 f s x v) s x v :=
  DifferentiableWithinAt.hasDerivWithinAt h

theorem LineDifferentiableAt.hasLineDerivAt (h : LineDifferentiableAt 𝕜 f x v) :
    HasLineDerivAt 𝕜 f (lineDeriv 𝕜 f x v) x v :=
  DifferentiableAt.hasDerivAt h

@[simp] lemma hasLineDerivWithinAt_univ :
    HasLineDerivWithinAt 𝕜 f f' univ x v ↔ HasLineDerivAt 𝕜 f f' x v := by
  simp only [HasLineDerivWithinAt, HasLineDerivAt, preimage_univ, hasDerivWithinAt_univ]

theorem lineDerivWithin_zero_of_not_lineDifferentiableWithinAt
    (h : ¬LineDifferentiableWithinAt 𝕜 f s x v) :
    lineDerivWithin 𝕜 f s x v = 0 :=
  derivWithin_zero_of_not_differentiableWithinAt h

theorem lineDeriv_zero_of_not_lineDifferentiableAt (h : ¬LineDifferentiableAt 𝕜 f x v) :
    lineDeriv 𝕜 f x v = 0 :=
  deriv_zero_of_not_differentiableAt h

theorem hasLineDerivAt_iff_isLittleO_nhds_zero :
    HasLineDerivAt 𝕜 f f' x v ↔
      (fun t : 𝕜 => f (x + t • v) - f x - t • f') =o[𝓝 0] fun t => t := by
  simp only [HasLineDerivAt, hasDerivAt_iff_isLittleO_nhds_zero, zero_add, zero_smul, add_zero]

theorem HasLineDerivAt.unique (h₀ : HasLineDerivAt 𝕜 f f₀' x v) (h₁ : HasLineDerivAt 𝕜 f f₁' x v) :
    f₀' = f₁' :=
  HasDerivAt.unique h₀ h₁

protected theorem HasLineDerivAt.lineDeriv (h : HasLineDerivAt 𝕜 f f' x v) :
    lineDeriv 𝕜 f x v = f' := by
  rw [h.unique h.lineDifferentiableAt.hasLineDerivAt]

theorem lineDifferentiableWithinAt_univ :
    LineDifferentiableWithinAt 𝕜 f univ x v ↔ LineDifferentiableAt 𝕜 f x v := by
  simp only [LineDifferentiableWithinAt, LineDifferentiableAt, preimage_univ,
    differentiableWithinAt_univ]

theorem LineDifferentiableAt.lineDifferentiableWithinAt (h : LineDifferentiableAt 𝕜 f x v) :
    LineDifferentiableWithinAt 𝕜 f s x v :=
  (differentiableWithinAt_univ.2 h).mono (subset_univ _)

@[simp]
theorem lineDerivWithin_univ : lineDerivWithin 𝕜 f univ x v = lineDeriv 𝕜 f x v := by
  simp [lineDerivWithin, lineDeriv]

theorem LineDifferentiableWithinAt.mono (h : LineDifferentiableWithinAt 𝕜 f t x v) (st : s ⊆ t) :
    LineDifferentiableWithinAt 𝕜 f s x v :=
  (h.hasLineDerivWithinAt.mono st).lineDifferentiableWithinAt

theorem HasLineDerivWithinAt.congr_mono (h : HasLineDerivWithinAt 𝕜 f f' s x v) (ht : EqOn f₁ f t)
    (hx : f₁ x = f x) (h₁ : t ⊆ s) : HasLineDerivWithinAt 𝕜 f₁ f' t x v :=
  HasDerivWithinAt.congr_mono h (fun y hy ↦ ht hy) (by simpa using hx) (preimage_mono h₁)

theorem HasLineDerivWithinAt.congr (h : HasLineDerivWithinAt 𝕜 f f' s x v) (hs : EqOn f₁ f s)
    (hx : f₁ x = f x) : HasLineDerivWithinAt 𝕜 f₁ f' s x v :=
  h.congr_mono hs hx (Subset.refl _)

theorem HasLineDerivWithinAt.congr' (h : HasLineDerivWithinAt 𝕜 f f' s x v)
    (hs : EqOn f₁ f s) (hx : x ∈ s) :
    HasLineDerivWithinAt 𝕜 f₁ f' s x v :=
  h.congr hs (hs hx)

theorem LineDifferentiableWithinAt.congr_mono (h : LineDifferentiableWithinAt 𝕜 f s x v)
    (ht : EqOn f₁ f t) (hx : f₁ x = f x) (h₁ : t ⊆ s) :
    LineDifferentiableWithinAt 𝕜 f₁ t x v :=
  (HasLineDerivWithinAt.congr_mono h.hasLineDerivWithinAt ht hx h₁).differentiableWithinAt

theorem LineDifferentiableWithinAt.congr (h : LineDifferentiableWithinAt 𝕜 f s x v)
    (ht : ∀ x ∈ s, f₁ x = f x) (hx : f₁ x = f x) :
    LineDifferentiableWithinAt 𝕜 f₁ s x v :=
  LineDifferentiableWithinAt.congr_mono h ht hx (Subset.refl _)

theorem lineDerivWithin_congr (hs : EqOn f₁ f s) (hx : f₁ x = f x) :
    lineDerivWithin 𝕜 f₁ s x v = lineDerivWithin 𝕜 f s x v :=
  derivWithin_congr (fun y hy ↦ hs hy) (by simpa using hx)

theorem lineDerivWithin_congr' (hs : EqOn f₁ f s) (hx : x ∈ s) :
    lineDerivWithin 𝕜 f₁ s x v = lineDerivWithin 𝕜 f s x v :=
  lineDerivWithin_congr hs (hs hx)

end Module

section NormedSpace

/-!
Results that need a normed space structure on `E`
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f f₀ f₁ : E → F} {f' : F} {s t : Set E} {x v : E} {L : E →L[𝕜] F}

theorem HasLineDerivWithinAt.mono_of_mem
    (h : HasLineDerivWithinAt 𝕜 f f' t x v) (hst : t ∈ 𝓝[s] x) :
    HasLineDerivWithinAt 𝕜 f f' s x v := by
  apply HasDerivWithinAt.mono_of_mem h
  apply ContinuousWithinAt.preimage_mem_nhdsWithin'' _ hst (by simp)
  apply Continuous.continuousWithinAt; continuity

theorem HasLineDerivWithinAt.hasLineDerivAt
    (h : HasLineDerivWithinAt 𝕜 f f' s x v) (hs : s ∈ 𝓝 x) :
    HasLineDerivAt 𝕜 f f' x v := by
  rw [← hasLineDerivWithinAt_univ]
  rw [← nhdsWithin_univ] at hs
  exact h.mono_of_mem hs

theorem LineDifferentiableWithinAt.lineDifferentiableAt (h : LineDifferentiableWithinAt 𝕜 f s x v)
    (hs : s ∈ 𝓝 x) : LineDifferentiableAt 𝕜 f x v :=
  (h.hasLineDerivWithinAt.hasLineDerivAt hs).lineDifferentiableAt

lemma HasFDerivWithinAt.hasLineDerivWithinAt (hf : HasFDerivWithinAt f L s x) :
    HasLineDerivWithinAt 𝕜 f (L v) s x v := by
  let F := fun (t : 𝕜) ↦ x + t • v
  rw [show x = F (0 : 𝕜) by simp] at hf
  have A : HasDerivWithinAt F (0 + (1 : 𝕜) • v) (F ⁻¹' s) 0 :=
    ((hasDerivAt_const (0 : 𝕜) x).add ((hasDerivAt_id' (0 : 𝕜)).smul_const v)).hasDerivWithinAt
  simp only [one_smul, zero_add] at A
  exact hf.comp_hasDerivWithinAt (x := (0 : 𝕜)) A (mapsTo_preimage F s)

lemma HasFDerivAt.hasLineDerivAt (hf : HasFDerivAt f L x) :
    HasLineDerivAt 𝕜 f (L v) x v := by
  rw [← hasLineDerivWithinAt_univ]
  exact hf.hasFDerivWithinAt.hasLineDerivWithinAt

theorem LineDifferentiableWithinAt.mono_of_mem (h : LineDifferentiableWithinAt 𝕜 f s x v)
    (hst : s ∈ 𝓝[t] x) : LineDifferentiableWithinAt 𝕜 f t x v :=
  (h.hasLineDerivWithinAt.mono_of_mem hst).lineDifferentiableWithinAt

theorem lineDerivWithin_of_mem_nhds (h : s ∈ 𝓝 x) :
    lineDerivWithin 𝕜 f s x v = lineDeriv 𝕜 f x v := by
  apply derivWithin_of_mem_nhds
  apply (Continuous.continuousAt _).preimage_mem_nhds (by simpa using h)
  continuity

theorem lineDerivWithin_of_open (hs : IsOpen s) (hx : x ∈ s) :
    lineDerivWithin 𝕜 f s x v = lineDeriv 𝕜 f x v :=
  lineDerivWithin_of_mem_nhds (hs.mem_nhds hx)

theorem hasLineDerivWithinAt_congr_set (h : s =ᶠ[𝓝 x] t) :
    HasLineDerivWithinAt 𝕜 f f' s x v ↔ HasLineDerivWithinAt 𝕜 f f' t x v := by
  apply hasDerivWithinAt_congr_set
  let F := fun (t : 𝕜) ↦ x + t • v
  have B : ContinuousAt F 0 := by apply Continuous.continuousAt; continuity
  have : s =ᶠ[𝓝 (F 0)] t := by convert h; simp
  exact B.preimage_mem_nhds this

theorem lineDifferentiableWithinAt_congr_set (h : s =ᶠ[𝓝 x] t) :
    LineDifferentiableWithinAt 𝕜 f s x v ↔ LineDifferentiableWithinAt 𝕜 f t x v :=
  ⟨fun h' ↦ ((hasLineDerivWithinAt_congr_set h).1
    h'.hasLineDerivWithinAt).lineDifferentiableWithinAt,
  fun h' ↦ ((hasLineDerivWithinAt_congr_set h.symm).1
    h'.hasLineDerivWithinAt).lineDifferentiableWithinAt⟩

theorem lineDerivWithin_congr_set (h : s =ᶠ[𝓝 x] t) :
    lineDerivWithin 𝕜 f s x v = lineDerivWithin 𝕜 f t x v := by
  apply derivWithin_congr_set
  let F := fun (t : 𝕜) ↦ x + t • v
  have B : ContinuousAt F 0 := by apply Continuous.continuousAt; continuity
  have : s =ᶠ[𝓝 (F 0)] t := by convert h; simp
  exact B.preimage_mem_nhds this

theorem Filter.EventuallyEq.hasLineDerivAt_iff (h : f₀ =ᶠ[𝓝 x] f₁) :
    HasLineDerivAt 𝕜 f₀ f' x v ↔ HasLineDerivAt 𝕜 f₁ f' x v := by
  apply hasDerivAt_iff
  let F := fun (t : 𝕜) ↦ x + t • v
  have B : ContinuousAt F 0 := by apply Continuous.continuousAt; continuity
  have : f₀ =ᶠ[𝓝 (F 0)] f₁ := by convert h; simp
  exact B.preimage_mem_nhds this

theorem Filter.EventuallyEq.lineDifferentiableAt_iff (h : f₀ =ᶠ[𝓝 x] f₁) :
    LineDifferentiableAt 𝕜 f₀ x v ↔ LineDifferentiableAt 𝕜 f₁ x v :=
  ⟨fun h' ↦ (h.hasLineDerivAt_iff.1 h'.hasLineDerivAt).lineDifferentiableAt,
  fun h' ↦ (h.hasLineDerivAt_iff.2 h'.hasLineDerivAt).lineDifferentiableAt⟩

theorem Filter.EventuallyEq.hasLineDerivWithinAt_iff (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : f₀ x = f₁ x) :
    HasLineDerivWithinAt 𝕜 f₀ f' s x v ↔ HasLineDerivWithinAt 𝕜 f₁ f' s x v := by
  apply hasDerivWithinAt_iff
  · have A : Continuous (fun (t : 𝕜) ↦ x + t • v) := by continuity
    exact A.continuousWithinAt.preimage_mem_nhdsWithin'' h (by simp)
  · simpa using hx

theorem Filter.EventuallyEq.hasLineDerivWithinAt_iff_of_mem (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : x ∈ s) :
    HasLineDerivWithinAt 𝕜 f₀ f' s x v ↔ HasLineDerivWithinAt 𝕜 f₁ f' s x v :=
  h.hasLineDerivWithinAt_iff (h.eq_of_nhdsWithin hx)

theorem Filter.EventuallyEq.lineDifferentiableWithinAt_iff
    (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : f₀ x = f₁ x) :
    LineDifferentiableWithinAt 𝕜 f₀ s x v ↔ LineDifferentiableWithinAt 𝕜 f₁ s x v :=
  ⟨fun h' ↦ ((h.hasLineDerivWithinAt_iff hx).1 h'.hasLineDerivWithinAt).lineDifferentiableWithinAt,
  fun h' ↦ ((h.hasLineDerivWithinAt_iff hx).2 h'.hasLineDerivWithinAt).lineDifferentiableWithinAt⟩

theorem Filter.EventuallyEq.lineDifferentiableWithinAt_iff_of_mem
    (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : x ∈ s) :
    LineDifferentiableWithinAt 𝕜 f₀ s x v ↔ LineDifferentiableWithinAt 𝕜 f₁ s x v :=
  h.lineDifferentiableWithinAt_iff (h.eq_of_nhdsWithin hx)

lemma HasLineDerivWithinAt.congr_of_eventuallyEq (hf : HasLineDerivWithinAt 𝕜 f f' s x v)
    (h'f : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : HasLineDerivWithinAt 𝕜 f₁ f' s x v := by
  apply HasDerivWithinAt.congr_of_eventuallyEq hf _ (by simp [hx])
  have A : Continuous (fun (t : 𝕜) ↦ x + t • v) := by continuity
  exact A.continuousWithinAt.preimage_mem_nhdsWithin'' h'f (by simp)

theorem HasLineDerivAt.congr_of_eventuallyEq (h : HasLineDerivAt 𝕜 f f' x v) (h₁ : f₁ =ᶠ[𝓝 x] f) :
    HasLineDerivAt 𝕜 f₁ f' x v := by
  apply HasDerivAt.congr_of_eventuallyEq h
  let F := fun (t : 𝕜) ↦ x + t • v
  rw [show x = F 0 by simp] at h₁
  exact (Continuous.continuousAt (by continuity)).preimage_mem_nhds h₁

theorem LineDifferentiableWithinAt.congr_of_eventuallyEq (h : LineDifferentiableWithinAt 𝕜 f s x v)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : LineDifferentiableWithinAt 𝕜 f₁ s x v :=
  (h.hasLineDerivWithinAt.congr_of_eventuallyEq h₁ hx).differentiableWithinAt

theorem LineDifferentiableAt.congr_of_eventuallyEq
    (h : LineDifferentiableAt 𝕜 f x v) (hL : f₁ =ᶠ[𝓝 x] f) :
    LineDifferentiableAt 𝕜 f₁ x v := by
  apply DifferentiableAt.congr_of_eventuallyEq h
  let F := fun (t : 𝕜) ↦ x + t • v
  rw [show x = F 0 by simp] at hL
  exact (Continuous.continuousAt (by continuity)).preimage_mem_nhds hL

theorem Filter.EventuallyEq.lineDerivWithin_eq (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    lineDerivWithin 𝕜 f₁ s x v = lineDerivWithin 𝕜 f s x v := by
  apply derivWithin_eq ?_ (by simpa using hx)
  have A : Continuous (fun (t : 𝕜) ↦ x + t • v) := by continuity
  exact A.continuousWithinAt.preimage_mem_nhdsWithin'' hs (by simp)

theorem Filter.EventuallyEq.lineDerivWithin_eq_nhds (h : f₁ =ᶠ[𝓝 x] f) :
    lineDerivWithin 𝕜 f₁ s x v = lineDerivWithin 𝕜 f s x v :=
  (h.filter_mono nhdsWithin_le_nhds).lineDerivWithin_eq h.self_of_nhds

theorem Filter.EventuallyEq.lineDeriv_eq (h : f₁ =ᶠ[𝓝 x] f) :
    lineDeriv 𝕜 f₁ x v = lineDeriv 𝕜 f x v := by
  rw [← lineDerivWithin_univ, ← lineDerivWithin_univ, h.lineDerivWithin_eq_nhds]


/-- Converse to the mean value inequality: if `f` is differentiable at `x₀` and `C`-lipschitz
on a neighborhood of `x₀` then its derivative at `x₀` has norm bounded by `C`. This version
only assumes that `‖f x - f x₀‖ ≤ C * ‖x - x₀‖` in a neighborhood of `x`. -/
theorem HasLineDerivAt.le_of_lip' {f : E → F} {f' : F} {x₀ : E} (hf : HasLineDerivAt 𝕜 f f' x₀ v)
    {C : ℝ} (hC₀ : 0 ≤ C) (hlip : ∀ᶠ x in 𝓝 x₀, ‖f x - f x₀‖ ≤ C * ‖x - x₀‖) :
    ‖f'‖ ≤ C * ‖v‖ := by
  have Z := HasDerivAt.le_of_lip'

#exit

/-- Converse to the mean value inequality: if `f` is differentiable at `x₀` and `C`-lipschitz
on a neighborhood of `x₀` then its derivative at `x₀` has norm bounded by `C`. -/
theorem HasFDerivAt.le_of_lip {f : E → F} {f' : E →L[𝕜] F} {x₀ : E} (hf : HasFDerivAt f f' x₀)
    {s : Set E} (hs : s ∈ 𝓝 x₀) {C : ℝ≥0} (hlip : LipschitzOnWith C f s) : ‖f'‖ ≤ C := by

end NormedSpace

section Zero

variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] {f : E → F} {s : Set E} {x : E}

theorem hasLineDerivWithinAt_zero : HasLineDerivWithinAt 𝕜 f 0 s x 0 := by
  simp [HasLineDerivWithinAt, hasDerivWithinAt_const]

theorem hasLineDerivAt_zero : HasLineDerivAt 𝕜 f 0 x 0 := by
  simp [HasLineDerivAt, hasDerivAt_const]

theorem lineDifferentiableWithinAt_zero : LineDifferentiableWithinAt 𝕜 f s x 0 :=
  hasLineDerivWithinAt_zero.lineDifferentiableWithinAt

theorem lineDifferentiableAt_zero : LineDifferentiableAt 𝕜 f x 0 :=
  hasLineDerivAt_zero.lineDifferentiableAt

theorem lineDeriv_zero : lineDeriv 𝕜 f x 0 = 0 :=
  hasLineDerivAt_zero.lineDeriv

end Zero

section CompRight

variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]
  {E' : Type*} [AddCommGroup E'] [Module 𝕜 E']
  {f : E → F} {f' : F} {x v : E'} {L : E' →ₗ[𝕜] E}

theorem HasLineDerivAt.of_comp {v : E'} (hf : HasLineDerivAt 𝕜 (f ∘ L) f' x v) :
    HasLineDerivAt 𝕜 f f' (L x) (L v) := by
  simpa [HasLineDerivAt] using hf

theorem LineDifferentiableAt.of_comp {v : E'} (hf : LineDifferentiableAt 𝕜 (f ∘ L) x v) :
    LineDifferentiableAt 𝕜 f (L x) (L v) :=
  hf.hasLineDerivAt.of_comp.lineDifferentiableAt

end CompRight
