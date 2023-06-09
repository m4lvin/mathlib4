/-
Copyright (c) 2023 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)

open Set

namespace NNReal

lemma strictConcaveOn_rpow {p : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1) :
    StrictConcaveOn ℝ≥0 univ fun x : ℝ≥0 => x ^ p := by
  have hp₀' : 0 < 1 / p := by positivity
  have hp₁' : 1 < 1 / p := by rw [one_lt_div hp₀]; exact hp₁
  let f := NNReal.orderIsoRpow (1 / p) hp₀'
  have h₁ : StrictConvexOn ℝ≥0 univ f := by
    refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
    exact (strictConvexOn_rpow hp₁').2 (by positivity : 0 ≤ x) (by positivity : 0 ≤ y)
      (by simp [hxy]) ha hb (by simp; norm_cast)
  have h₂ : ∀ x, f.symm x = x ^ p := by simp [NNReal.orderIsoRpow_symm_eq]
  refine ⟨convex_univ, fun x _ y _ hxy a b ha hb hab => ?_⟩
  simp only [←h₂]
  exact (strictConcaveOn_orderIso_symm f h₁).2 (Set.mem_univ x) (Set.mem_univ y) hxy ha hb hab

lemma concaveOn_rpow {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    ConcaveOn ℝ≥0 univ fun x : ℝ≥0 => x ^ p := by
  sorry

lemma strictConcaveOn_sqrt : StrictConcaveOn ℝ≥0 univ NNReal.sqrt := by
  have : NNReal.sqrt = fun (x:ℝ≥0) => x ^ (1 / (2:ℝ)) := by
    ext x; exact_mod_cast NNReal.sqrt_eq_rpow x
  rw [this]
  exact strictConcaveOn_rpow (by positivity) (by linarith)

end NNReal

namespace Real

open NNReal

lemma strictConcaveOn_rpow {p : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1) :
    StrictConcaveOn ℝ (Set.Ici 0) fun x : ℝ => x ^ p := by
  refine ⟨convex_Ici _, fun x hx y hy hxy a b ha hb hab => ?_⟩
  let x' : ℝ≥0 := ⟨x, hx⟩
  let y' : ℝ≥0 := ⟨y, hy⟩
  let a' : ℝ≥0 := ⟨a, by positivity⟩
  let b' : ℝ≥0 := ⟨b, by positivity⟩
  have hx' : (fun z => z ^ p) x = (fun z => z ^ p) x' := rfl
  have hy' : (fun z => z ^ p) y = (fun z => z ^ p) y' := rfl
  have hxy' : x' ≠ y' := sorry
  have hab' : a' + b' = 1 := sorry
  rw [hx', hy']
  exact (NNReal.strictConcaveOn_rpow hp₀ hp₁).2 (Set.mem_univ x') (Set.mem_univ y')
    hxy' (by exact_mod_cast ha) (by exact_mod_cast hb) hab'

lemma concaveOn_rpow {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : 1 ≤ p) :
    ConcaveOn ℝ (Set.Ici 0) fun x : ℝ => x ^ p := by
  sorry

lemma strictConcaveOn_sqrt : StrictConcaveOn ℝ (Set.Ici 0) Real.sqrt := by
  have : Real.sqrt = fun (x:ℝ) => x ^ (1 / (2:ℝ)) := by
    ext x; exact Real.sqrt_eq_rpow x
  rw [this]
  exact strictConcaveOn_rpow (by positivity) (by linarith)

end Real
