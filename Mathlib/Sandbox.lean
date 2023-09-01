import Mathlib.Analysis.Convex.Basic

example (𝕜 : Type*) {E : Type*} [LinearOrderedRing 𝕜] [AddCommMonoid E] [SMul 𝕜 E] {f : E → 𝕜}
    (hf1 : ∀ x y, f (x + y) ≤ f x + f y) (hf2 : ∀ c x, f (c • x) ≤ |c| * f x) (B : 𝕜) :
    Convex 𝕜 { x | f x ≤ B } := by
  rw [convex_iff_segment_subset]
  rintro x hx y hy z ⟨a, b, ha, hb, hs, rfl⟩
  calc
    _ ≤ |a| • (f x) + |b| • (f y) := le_trans (hf1 _ _) (add_le_add (hf2 a x) (hf2 b y))
    _ ≤ a • B + b • B := ?_
    _ ≤ B := ?_
  · convert
      add_le_add (smul_le_smul_of_nonneg hx (abs_nonneg a)) (smul_le_smul_of_nonneg hy (abs_nonneg b))
    exact (abs_eq_self.mpr ha).symm
    exact (abs_eq_self.mpr hb).symm
  · rw [← add_smul, hs, one_smul]

#exit

  refine le_trans (hf1 _ _) ?_
  rw [hf2, hf2]


  sorry
