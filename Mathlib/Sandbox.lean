import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.NormedSpace.PiLp

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

theorem MeasurableEquiv.piCongrLeft {α β : Type*} (e : α ≃ β) (γ : Type*) [MeasurableSpace γ] :
    (α → γ) ≃ᵐ (β → γ) := by
