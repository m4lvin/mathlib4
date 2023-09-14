/-
Copyright (c) 2023 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Tactic

/-!
# Integration of bounded continuous functions

This file contains some results about integrals of bounded continuous functions.
-/

open MeasureTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction Topology

section moved_from_FiniteMeasure
-- These were moved (now in fact only copied) from `Mathlib.MeasureTheory.Measure.FiniteMeasure`.

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]

theorem _root_.BoundedContinuousFunction.NNReal.coe_ennreal_comp_measurable (f : X →ᵇ ℝ≥0) :
    Measurable fun X => (f X : ℝ≥0∞) :=
  measurable_coe_nnreal_ennreal.comp f.continuous.measurable
#align bounded_continuous_function.nnreal.to_ennreal_comp_measurable BoundedContinuousFunction.NNReal.coe_ennreal_comp_measurable

namespace MeasureTheory

variable (μ : Measure X) [IsFiniteMeasure μ]

theorem lintegral_lt_top_of_boundedContinuous_to_nnreal (f : X →ᵇ ℝ≥0) :
    (∫⁻ X, f X ∂μ) < ∞ := by
  apply IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal
  use nndist f 0
  intro x
  have key := BoundedContinuousFunction.Nnreal.upper_bound f x
  rw [ENNReal.coe_le_coe]
  have eq : nndist f 0 = ⟨dist f 0, dist_nonneg⟩ := by
    ext
    simp only [Real.coe_toNNReal', max_eq_left_iff, NNReal.coe_mk, coe_nndist]
  rwa [eq] at key
#align measure_theory.lintegral_lt_top_of_bounded_continuous_to_nnreal MeasureTheory.lintegral_lt_top_of_boundedContinuous_to_nnreal

theorem FiniteMeasure.integrable_of_boundedContinuous_to_nnreal (f : X →ᵇ ℝ≥0) :
    Integrable (((↑) : ℝ≥0 → ℝ) ∘ ⇑f) μ := by
  refine' ⟨(NNReal.continuous_coe.comp f.continuous).measurable.aestronglyMeasurable, _⟩
  simp only [HasFiniteIntegral, Function.comp_apply, NNReal.nnnorm_eq]
  exact lintegral_lt_top_of_boundedContinuous_to_nnreal _ f
#align measure_theory.finite_measure.integrable_of_bounded_continuous_to_nnreal MeasureTheory.FiniteMeasure.integrable_of_boundedContinuous_to_nnreal

/-
theorem FiniteMeasure.integrable_of_boundedContinuous_to_real (f : X →ᵇ ℝ) :
    Integrable (⇑f) μ := by
  refine' ⟨f.continuous.measurable.aestronglyMeasurable, _⟩
  have aux : ((↑) : ℝ≥0 → ℝ) ∘ ⇑f.nnnorm = fun x => ‖f x‖ := by
    ext X
    simp only [Function.comp_apply, BoundedContinuousFunction.nnnorm_coeFn_eq, coe_nnnorm]
  apply (hasFiniteIntegral_iff_norm f).mpr
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · exact ENNReal.ofReal_lt_top
  · exact aux ▸ integrable_of_boundedContinuous_to_nnreal μ f.nnnorm
  · exact eventually_of_forall fun X => norm_nonneg (f X)
#align measure_theory.finite_measure.integrable_of_bounded_continuous_to_real MeasureTheory.FiniteMeasure.integrable_of_boundedContinuous_to_real
 -/

end MeasureTheory

end moved_from_FiniteMeasure



section boundedness_by_norm_bounds

lemma Metric.bounded_range_of_forall_norm_le {ι : Type*} {E : Type*} [NormedAddGroup E]
    {f : ι → E} {c : ℝ} (h : ∀ i, ‖f i‖ ≤ c) :
    Metric.Bounded (Set.range f) := by
  apply Metric.Bounded.mono _ (@Metric.bounded_closedBall _ _ 0 c)
  intro x ⟨i, hi⟩
  simpa only [← hi, Metric.closedBall, dist_zero_right, Set.mem_setOf_eq, ge_iff_le] using h i

end boundedness_by_norm_bounds



section

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]

/-
-- TODO: Is it possible to add a @[gcongr] attribute to `lintegral_mono`?

lemma foo (μ : Measure X) {f g : X → ℝ≥0∞} (hfg : f ≤ g) :
    ∫⁻ X, f X ∂μ ≤ ∫⁻ X, g X ∂μ := by
  gcongr -- gcongr did not make progress
  sorry

attribute [gcongr] lintegral_mono -- @[gcongr] attribute only applies to lemmas proving x₁ ~₁ x₁' → ... xₙ ~ₙ xₙ' → f x₁ ... xₙ ∼ f x₁' ... xₙ', got ∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} ⦃f g : α → ℝ≥0∞⦄, f ≤ g → ∫⁻ (a : α), f a ∂μ ≤ ∫⁻ (a : α), g a ∂μ

-- This would solve it!

lemma MeasureTheory.lintegral_mono'' {α : Type} {m : MeasurableSpace α}
    {μ : MeasureTheory.Measure α} {f g : α → ℝ≥0∞} (hfg : f ≤ g) :
    lintegral μ f ≤ lintegral μ g :=
  lintegral_mono hfg

attribute [gcongr] MeasureTheory.lintegral_mono''

#check lintegral_mono
#check lintegral_mono''
 -/

lemma MeasureTheory.lintegral_mono'' {α : Type*} {m : MeasurableSpace α}
    {μ : MeasureTheory.Measure α} {f g : α → ℝ≥0∞} (hfg : f ≤ g) :
    lintegral μ f ≤ lintegral μ g :=
  lintegral_mono hfg

attribute [gcongr] MeasureTheory.lintegral_mono''

variable {E : Type*} [NormedAddCommGroup E] [TopologicalSpace.SecondCountableTopology E]
variable [MeasurableSpace E] [BorelSpace E]

lemma BoundedContinuousFunction.integrable (μ : Measure X) [IsFiniteMeasure μ] (f : X →ᵇ E) :
    Integrable f μ := by
  refine ⟨f.continuous.measurable.aestronglyMeasurable, (hasFiniteIntegral_def _ _).mp ?_⟩
  calc  ∫⁻ x, ‖f x‖₊ ∂μ
    _ ≤ ∫⁻ _, ‖f‖₊ ∂μ                       := ?_
    _ = ‖f‖₊ * (μ Set.univ)                 := by rw [lintegral_const]
    _ < ∞                                   := ENNReal.mul_lt_top
                                                ENNReal.coe_ne_top (measure_ne_top μ Set.univ)
  · --gcongr -- or `apply lintegral_mono`
    apply lintegral_mono
    exact fun x ↦ ENNReal.coe_le_coe.mpr (nnnorm_coe_le_nnnorm f x)

variable [NormedSpace ℝ E]

lemma BoundedContinuousFunction.norm_integral_le_mul_norm_of_isFiniteMeasure
    (μ : Measure X) [IsFiniteMeasure μ] (f : X →ᵇ E) :
    ‖∫ x, (f x) ∂μ‖ ≤ ENNReal.toReal (μ Set.univ) * ‖f‖ := by
  calc  ‖∫ x, (f x) ∂μ‖
    _ ≤ ∫ x, ‖f x‖ ∂μ                       := by exact norm_integral_le_integral_norm _
    _ ≤ ∫ _, ‖f‖ ∂μ                         := ?_
    _ = ENNReal.toReal (μ Set.univ) • ‖f‖   := by rw [integral_const]
  · apply integral_mono _ (integrable_const ‖f‖) (fun x ↦ f.norm_coe_le_norm x)
    exact (integrable_norm_iff f.continuous.measurable.aestronglyMeasurable).mpr (f.integrable μ)

lemma BoundedContinuousFunction.norm_integral_le_norm_of_isProbabilityMeasure
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X →ᵇ E) :
    ‖∫ x, (f x) ∂μ‖ ≤ ‖f‖ := by
  convert f.norm_integral_le_mul_norm_of_isFiniteMeasure μ
  simp only [measure_univ, ENNReal.one_toReal, one_mul]

lemma bounded_range_integral_boundedContinuousFunction_of_isProbabilityMeasure
    {ι : Type*} (μs : ι → Measure X) [∀ i, IsProbabilityMeasure (μs i)] (f : X →ᵇ E) :
    Metric.Bounded (Set.range (fun i ↦ ∫ x, (f x) ∂ (μs i))) := by
  apply Metric.bounded_range_of_forall_norm_le (c := ‖f‖)
  exact fun i ↦ f.norm_integral_le_norm_of_isProbabilityMeasure (μs i)

end

section

variable {X : Type*} [TopologicalSpace X]

lemma BoundedContinuousFunction.neg_norm_le (f : X →ᵇ ℝ) (x : X) :
    -‖f‖ ≤ f x := (abs_le.mp (norm_coe_le_norm f x)).1

lemma BoundedContinuousFunction.le_norm (f : X →ᵇ ℝ) (x : X):
    f x ≤ ‖f‖ := (abs_le.mp (norm_coe_le_norm f x)).2

lemma BoundedContinuousFunction.add_norm_nonneg (f : X →ᵇ ℝ) :
    0 ≤ f + BoundedContinuousFunction.const _ ‖f‖ := by
  intro x
  dsimp
  linarith [(abs_le.mp (norm_coe_le_norm f x)).1]

lemma BoundedContinuousFunction.norm_sub_nonneg (f : X →ᵇ ℝ) :
    0 ≤ BoundedContinuousFunction.const _ ‖f‖ - f := by
  intro x
  dsimp
  linarith [(abs_le.mp (norm_coe_le_norm f x)).2]

variable [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

lemma BoundedContinuousFunction.integral_add_const (f : X →ᵇ ℝ) (c : ℝ) :
    ∫ x, (f + BoundedContinuousFunction.const X c) x ∂μ =
      ∫ x, f x ∂μ + ENNReal.toReal (μ (Set.univ)) • c := by
  simp [integral_add (f.integrable _) (integrable_const c)]

lemma BoundedContinuousFunction.integral_const_sub (f : X →ᵇ ℝ) (c : ℝ) :
    ∫ x, (BoundedContinuousFunction.const X c - f) x ∂μ =
      ENNReal.toReal (μ (Set.univ)) • c - ∫ x, f x ∂μ := by
  simp [integral_sub (integrable_const c) (f.integrable _)]

end
