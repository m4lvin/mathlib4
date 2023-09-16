-- import Mathlib
import Mathlib.Analysis.NormedSpace.PiLp
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

theorem Convex_subAdditive (𝕜 : Type*) {E : Type*} [LinearOrderedRing 𝕜] [AddCommMonoid E]
    [SMul 𝕜 E] {f : E → 𝕜} (hf1 : ∀ x y, f (x + y) ≤ (f x) + (f y))
    (hf2 : ∀ ⦃c⦄ x, 0 ≤ c → f (c • x) ≤ c * f x) (B : 𝕜) :
    Convex 𝕜 { x | f x ≤ B } := by
  rw [convex_iff_segment_subset]
  rintro x hx y hy z ⟨a, b, ha, hb, hs, rfl⟩
  calc
    _ ≤ a • (f x) + b • (f y) := le_trans (hf1 _ _) (add_le_add (hf2 x ha) (hf2 y hb))
    _ ≤ a • B + b • B := add_le_add (smul_le_smul_of_nonneg hx ha) (smul_le_smul_of_nonneg hy hb)
    _ ≤ B := by rw [← add_smul, hs, one_smul]

open MeasureTheory MeasureTheory.Measure

@[simp]
theorem Basis.parallelepiped_isEmpty {ι : Type*} [IsEmpty ι] :
    (Basis.parallelepiped (Pi.basisFun ℝ ι) : Set (ι → ℝ)) = Set.univ := by
  ext; simp [mem_parallelepiped_iff]

@[simp]
theorem Real.volume_pi_isEmpty {ι : Type*} [IsEmpty ι] : volume (@Set.univ (ι → ℝ)) = 1 := by
  rw [← addHaarMeasure_eq_volume_pi, ← Basis.parallelepiped_isEmpty, Basis.parallelepiped_basisFun]
  exact addHaarMeasure_self


#exit

theorem Measurable.piCongrLeft {α β : Type*} (e : α ≃ β) (γ : Type*) [MeasurableSpace γ] :
    Measurable (Equiv.piCongrLeft (fun _ => γ) e) := by
  refine measurable_pi_lambda _ (fun a => ?_)
  simp_rw [Equiv.piCongrLeft_apply, eq_rec_constant]
  exact measurable_pi_apply _

def MeasurableEquiv.piCongrLeft {α β : Type*} (e : α ≃ β) (γ : Type*) [MeasurableSpace γ] :
    (α → γ) ≃ᵐ (β → γ) :=
{ Equiv.piCongrLeft (fun _ => γ) e with
  measurable_toFun := fun _ h => (Measurable.piCongrLeft e γ) h
  measurable_invFun := by
    intro _ h
    simp
    convert (Measurable.piCongrLeft e.symm γ) h

    dsimp

}
