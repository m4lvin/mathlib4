/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.GeomSum
import Mathlib.Data.Polynomial.Monic
import Mathlib.Data.Polynomial.Eval
import Mathlib.Data.Nat.Factorial.SuperFactorial
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

#align_import linear_algebra.vandermonde from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Vandermonde matrix

This file defines the `vandermonde` matrix and gives its determinant.

## Main definitions

 - `vandermonde v`: a square matrix with the `i, j`th entry equal to `v i ^ j`.

## Main results

 - `det_vandermonde`: `det (vandermonde v)` is the product of `v i - v j`, where
   `(i, j)` ranges over the unordered pairs.
 - `superFactorial_dvd_vandermonde_det`: The superfactorial divides the `det (vandermonde v)`.
    The proofs follows [R. Chapman, *A Polynomial Taking Integer Values*](chapman1996).
-/


variable {R : Type*} [CommRing R]

open Equiv Finset

open BigOperators Matrix

namespace Matrix

/-- `vandermonde v` is the square matrix with `i`th row equal to `1, v i, v i ^ 2, v i ^ 3, ...`.
-/
def vandermonde {n : ℕ} (v : Fin n → R) : Matrix (Fin n) (Fin n) R := fun i j => v i ^ (j : ℕ)
#align matrix.vandermonde Matrix.vandermonde

@[simp]
theorem vandermonde_apply {n : ℕ} (v : Fin n → R) (i j) : vandermonde v i j = v i ^ (j : ℕ) :=
  rfl
#align matrix.vandermonde_apply Matrix.vandermonde_apply

@[simp]
theorem vandermonde_cons {n : ℕ} (v0 : R) (v : Fin n → R) :
    vandermonde (Fin.cons v0 v : Fin n.succ → R) =
      Fin.cons (fun (j : Fin n.succ) => v0 ^ (j : ℕ)) fun i => Fin.cons 1
      fun j => v i * vandermonde v i j := by
  ext i j
  refine' Fin.cases (by simp) (fun i => _) i
  refine' Fin.cases (by simp) (fun j => _) j
  simp [pow_succ]
#align matrix.vandermonde_cons Matrix.vandermonde_cons

theorem vandermonde_succ {n : ℕ} (v : Fin n.succ → R) :
    vandermonde v =
      Fin.cons (fun (j : Fin n.succ) => v 0 ^ (j : ℕ)) fun i =>
        Fin.cons 1 fun j => v i.succ * vandermonde (Fin.tail v) i j := by
  conv_lhs => rw [← Fin.cons_self_tail v, vandermonde_cons]
#align matrix.vandermonde_succ Matrix.vandermonde_succ

theorem vandermonde_mul_vandermonde_transpose {n : ℕ} (v w : Fin n → R) (i j) :
    (vandermonde v * (vandermonde w)ᵀ) i j = ∑ k : Fin n, (v i * w j) ^ (k : ℕ) := by
  simp only [vandermonde_apply, Matrix.mul_apply, Matrix.transpose_apply, mul_pow]
#align matrix.vandermonde_mul_vandermonde_transpose Matrix.vandermonde_mul_vandermonde_transpose

theorem vandermonde_transpose_mul_vandermonde {n : ℕ} (v : Fin n → R) (i j) :
    ((vandermonde v)ᵀ * vandermonde v) i j = ∑ k : Fin n, v k ^ (i + j : ℕ) := by
  simp only [vandermonde_apply, Matrix.mul_apply, Matrix.transpose_apply, pow_add]
#align matrix.vandermonde_transpose_mul_vandermonde Matrix.vandermonde_transpose_mul_vandermonde

theorem det_vandermonde {n : ℕ} (v : Fin n → R) :
    det (vandermonde v) = ∏ i : Fin n, Finset.prod (Ioi i) (fun j => v j - v i) := by
  unfold vandermonde
  induction' n with n ih
  · exact det_eq_one_of_card_eq_zero (Fintype.card_fin 0)
  calc
    det (of fun i j : Fin n.succ => v i ^ (j : ℕ)) =
        det
          (of fun i j : Fin n.succ =>
            Matrix.vecCons (v 0 ^ (j : ℕ)) (fun i => v (Fin.succ i) ^ (j : ℕ) - v 0 ^ (j : ℕ)) i) :=
      det_eq_of_forall_row_eq_smul_add_const (Matrix.vecCons 0 1) 0 (Fin.cons_zero _ _) ?_
    _ =
        det
          (of fun i j : Fin n =>
            Matrix.vecCons (v 0 ^ (j.succ : ℕ))
              (fun i : Fin n => v (Fin.succ i) ^ (j.succ : ℕ) - v 0 ^ (j.succ : ℕ))
              (Fin.succAbove 0 i)) := by
      simp_rw [det_succ_column_zero, Fin.sum_univ_succ, of_apply, Matrix.cons_val_zero, submatrix,
        of_apply, Matrix.cons_val_succ, Fin.val_zero, pow_zero, one_mul, sub_self,
        mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
    _ =
        det
          (of fun i j : Fin n =>
              (v (Fin.succ i) - v 0) *
                ∑ k in Finset.range (j + 1 : ℕ), v i.succ ^ k * v 0 ^ (j - k : ℕ) :
            Matrix _ _ R) := by
      congr
      ext i j
      rw [Fin.succAbove_zero, Matrix.cons_val_succ, Fin.val_succ, mul_comm]
      exact (geom_sum₂_mul (v i.succ) (v 0) (j + 1 : ℕ)).symm
    _ =
        (Finset.prod Finset.univ (fun i => v (Fin.succ i) - v 0)) *
          det fun i j : Fin n =>
            ∑ k in Finset.range (j + 1 : ℕ), v i.succ ^ k * v 0 ^ (j - k : ℕ) :=
      (det_mul_column (fun i => v (Fin.succ i) - v 0) _)
    _ = (Finset.prod Finset.univ (fun i => v (Fin.succ i) - v 0)) *
    det fun i j : Fin n => v (Fin.succ i) ^ (j : ℕ) := congr_arg _ ?_
    _ = ∏ i : Fin n.succ, Finset.prod (Ioi i) (fun j => v j - v i) := by
      simp_rw [Fin.prod_univ_succ, Fin.prod_Ioi_zero, Fin.prod_Ioi_succ]
      have h := ih (v ∘ Fin.succ)
      unfold Function.comp at h
      rw [h]

  · intro i j
    simp_rw [of_apply]
    rw [Matrix.cons_val_zero]
    refine' Fin.cases _ (fun i => _) i
    · simp
    rw [Matrix.cons_val_succ, Matrix.cons_val_succ, Pi.one_apply]
    ring
  · cases n
    · rw [det_eq_one_of_card_eq_zero (Fintype.card_fin 0),
      det_eq_one_of_card_eq_zero (Fintype.card_fin 0)]
    apply det_eq_of_forall_col_eq_smul_add_pred fun _ => v 0
    · intro j
      simp
    · intro i j
      simp only [smul_eq_mul, Pi.add_apply, Fin.val_succ, Fin.coe_castSucc, Pi.smul_apply]
      rw [Finset.sum_range_succ, add_comm, tsub_self, pow_zero, mul_one, Finset.mul_sum]
      congr 1
      refine' Finset.sum_congr rfl fun i' hi' => _
      rw [mul_left_comm (v 0), Nat.succ_sub, pow_succ]
      exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hi')
#align matrix.det_vandermonde Matrix.det_vandermonde

theorem det_vandermonde_eq_zero_iff [IsDomain R] {n : ℕ} {v : Fin n → R} :
    det (vandermonde v) = 0 ↔ ∃ i j : Fin n, v i = v j ∧ i ≠ j := by
  constructor
  · simp only [det_vandermonde v, Finset.prod_eq_zero_iff, sub_eq_zero, forall_exists_index]
    rintro i ⟨_, j, h₁, h₂⟩
    exact ⟨j, i, h₂, (mem_Ioi.mp h₁).ne'⟩
  · simp only [Ne.def, forall_exists_index, and_imp]
    refine' fun i j h₁ h₂ => Matrix.det_zero_of_row_eq h₂ (funext fun k => _)
    rw [vandermonde_apply, vandermonde_apply, h₁]
#align matrix.det_vandermonde_eq_zero_iff Matrix.det_vandermonde_eq_zero_iff

theorem det_vandermonde_ne_zero_iff [IsDomain R] {n : ℕ} {v : Fin n → R} :
    det (vandermonde v) ≠ 0 ↔ Function.Injective v := by
  unfold Function.Injective
  simp only [det_vandermonde_eq_zero_iff, Ne.def, not_exists, not_and, Classical.not_not]
#align matrix.det_vandermonde_ne_zero_iff Matrix.det_vandermonde_ne_zero_iff

theorem det_vandermonde_eq_det_vandermonde_add {n : ℕ} (v : Fin n → R) (a : R) :
    (Matrix.vandermonde v).det = (Matrix.vandermonde fun i ↦ v i + a).det := by
  simp [Matrix.det_vandermonde]

theorem det_vandermonde_eq_det_vandermonde_sub {n : ℕ} (v : Fin n → R) (a : R) :
    (Matrix.vandermonde v).det = (Matrix.vandermonde fun i ↦ v i - a).det := by
  rw [det_vandermonde_eq_det_vandermonde_add v (- a)]
  simp only [← sub_eq_add_neg]

theorem eq_zero_of_forall_index_sum_pow_mul_eq_zero {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    {f v : Fin n → R} (hf : Function.Injective f)
    (hfv : ∀ j, (∑ i : Fin n, f j ^ (i : ℕ) * v i) = 0) : v = 0 :=
  eq_zero_of_mulVec_eq_zero (det_vandermonde_ne_zero_iff.mpr hf) (funext hfv)
#align matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero Matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero

theorem eq_zero_of_forall_index_sum_mul_pow_eq_zero {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    {f v : Fin n → R} (hf : Function.Injective f) (hfv : ∀ j, (∑ i, v i * f j ^ (i : ℕ)) = 0) :
    v = 0 := by
  apply eq_zero_of_forall_index_sum_pow_mul_eq_zero hf
  simp_rw [mul_comm]
  exact hfv
#align matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero Matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero

theorem eq_zero_of_forall_pow_sum_mul_pow_eq_zero {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    {f v : Fin n → R} (hf : Function.Injective f)
    (hfv : ∀ i : Fin n, (∑ j : Fin n, v j * f j ^ (i : ℕ)) = 0) : v = 0 :=
  eq_zero_of_vecMul_eq_zero (det_vandermonde_ne_zero_iff.mpr hf) (funext hfv)
#align matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero

open Polynomial

theorem eval_matrix_of_polynomials_eq_vandermonde_mul_matrix_of_polynomials{n : ℕ}
    (v : Fin n → R) (p : Fin n → R[X]) (h_deg : ∀ i, (p i).natDegree = i) :
    Matrix.of (fun i j => ((p j).eval (v i))) =
    (Matrix.vandermonde v) * (Matrix.of (fun (i j : Fin n) => (p j).coeff i)) := by
  ext i j
  rw [Matrix.mul_apply, Polynomial.eval, Matrix.of_apply, Polynomial.eval₂]
  simp only [eq_intCast, Int.cast_id, Matrix.vandermonde]
  have : (p j).support ⊆ range n := supp_subset_range <| h_deg j ▸ Fin.prop j
  rw [sum_eq_of_subset _ (fun j => zero_mul ((v i) ^ j)) this, ← Fin.sum_univ_eq_sum_range]
  congr
  ext k
  rw [mul_comm, Matrix.of_apply, RingHom.id_apply]

theorem matrix_of_polynomials_blockTriangular {n : ℕ} (p : Fin n → R[X])
    (h_deg : ∀ i, (p i).natDegree  = i) :
    Matrix.BlockTriangular (Matrix.of (fun (i j : Fin n) => (p j).coeff i)) id :=
  fun _ j h => coeff_eq_zero_of_natDegree_lt (h_deg j ▸ h)

theorem det_matrix_of_polynomials {n : ℕ} (p : Fin n → R[X])
    (h_deg : ∀ i, (p i).natDegree  = i) (h_monic : ∀ i,  Monic <| p i) :
    (Matrix.of (fun (i j : Fin n) => (p j).coeff i)).det = 1 := by
  rw [Matrix.det_of_upperTriangular (matrix_of_polynomials_blockTriangular p h_deg)]
  convert prod_const_one
  rw [Matrix.of_apply]
  rename_i x _
  convert h_monic x
  unfold Monic leadingCoeff
  rw [h_deg x]

theorem vandermonde_det_eq_eval_matrix_of_polynomials_det {n : ℕ} (v : Fin n → R) (p : Fin n → R[X])
    (h_deg : ∀ i, (p i).natDegree  = i) (h_monic : ∀ i,  Monic <| p i) :
    (Matrix.vandermonde v).det = (Matrix.of (fun i j => ((p j).eval (v i)))).det := by
  rw [eval_matrix_of_polynomials_eq_vandermonde_mul_matrix_of_polynomials v p h_deg, Matrix.det_mul,
      det_matrix_of_polynomials p h_deg h_monic, mul_one]


/--
TOOD: this is similar to pochhammer, bu descending
check how this can be re-used instead of this adhoc definition
 -/
noncomputable
def polynomial_descFactorial : ℕ  →  ℤ[X]
 | 0 => (1 : ℤ[X])
 | n + 1 => (X - (n : ℤ[X])) * polynomial_descFactorial n

theorem descFatorial_eq_polynomial_descFactorial_eval (n k : ℕ) :
    ((polynomial_descFactorial k).eval (n : ℤ)) = (Nat.descFactorial n k)  := by
  induction' k with k hk
  · simp only [Nat.zero_eq, CharP.cast_eq_zero, polynomial_descFactorial, eval_mul, eval_sub,
      eval_X, eval_nat_cast, zero_sub, neg_mul, Nat.descFactorial_zero, Nat.cast_one, eval_one]
  · simp only [polynomial_descFactorial, eval_mul, eval_sub, eval_X, eval_nat_cast,
      Nat.descFactorial_succ, Nat.cast_mul]
    simp at hk
    rw [hk]
    simp only [mul_eq_mul_right_iff, Nat.cast_eq_zero, Nat.descFactorial_eq_zero_iff_lt]
    by_cases n < k
    · tauto
    · left
      simp at h
      exact (Int.ofNat_sub h).symm

theorem polynomial_descFactorial_monic (n : ℕ) : Monic <| polynomial_descFactorial n := by
  induction' n with n hn
  · rw [polynomial_descFactorial]
    exact monic_one
  · rw [polynomial_descFactorial]
    refine' Monic.mul _ hn
    exact monic_X_sub_C _

theorem polynomial_descFactorial_degree (n : ℕ) : (polynomial_descFactorial n).natDegree = n := by
  induction' n with n hn
  · rw [polynomial_descFactorial]
    simp [degree_one, Nat.zero_eq, CharP.cast_eq_zero]
  · rw [polynomial_descFactorial]
    rw [natDegree_mul, hn, add_comm]
    · norm_num
      congr
      rw [Nat.succ_eq_add_one]
      rw [add_right_inj]
      convert natDegree_X_sub_C _
      exact Int.instNontrivialInt
    · refine X_sub_C_ne_zero _
    · induction' n with n _
      · simp [polynomial_descFactorial]
      · have : 0 < n.succ := by exact Nat.succ_pos n
        rw [← hn] at this
        refine' ne_zero_of_natDegree_gt this

theorem eval_matrix_of_polynomials_eq_mul_matrix_of_choose {n : ℕ} (v : Fin n → ℕ) :
    (Matrix.of (fun (i j : Fin n) =>
    ((fun n => polynomial_descFactorial n) j).eval ((fun k => (v k : ℤ)) i)) ).det =
    (∏ i : Fin n,  Nat.factorial i) *
    (Matrix.of (fun (i j : Fin n)  => ((Nat.choose ((v i)) (j : ℕ)) : ℤ))).det := by
  convert Matrix.det_mul_row (fun (i : Fin n)  => ((Nat.factorial (i : ℕ)):ℤ)) _
  · rw [Matrix.of_apply, descFatorial_eq_polynomial_descFactorial_eval _ _]
    congr
    exact Nat.descFactorial_eq_factorial_mul_choose _ _
  · rw [Nat.cast_prod]

theorem superFactorial_eq_prod (n : ℕ) :
    Nat.superFactorial n = (∏ i : Fin (n + 1),  Nat.factorial i) := by
  induction' n with n hn
  · rfl
  · rw [Nat.superFactorial, hn, Fin.prod_univ_castSucc, mul_comm, Fin.prod_univ_castSucc,
        Fin.prod_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last, Nat.factorial, Nat.add_eq, add_zero]

theorem superFactorial_dvd_vandermonde_det {n : ℕ} (v : Fin (n + 1) → ℤ) :
   ↑(Nat.superFactorial n) ∣ (Matrix.vandermonde v).det := by
  let m' := List.minimum ((univ : Finset (Fin (n + 1))).image v).toList
  have : ((univ : Finset (Fin (n + 1))).image v).toList ≠ List.nil := by
    simp only [ne_eq, toList_eq_nil, image_eq_empty]
    refine Nonempty.ne_empty univ_nonempty
  cases' Option.isSome_iff_exists.mp <| Option.ne_none_iff_isSome.mp <|
      List.minimum_ne_top_of_ne_nil this with m hm
  have h_min : ∀  l, l ∈ ((univ : Finset (Fin (n + 1))).image v).toList →  m' ≤ l := by
     exact fun l a ↦ List.le_minimum_of_mem' a
  let w' := fun i ↦ (v i - m).toNat
  have h1 := eval_matrix_of_polynomials_eq_mul_matrix_of_choose w'
  rw [superFactorial_eq_prod]
  have h2 := vandermonde_det_eq_eval_matrix_of_polynomials_det (fun i ↦ ↑(w' i))
      (fun i => polynomial_descFactorial (i : ℕ))
      (fun i => polynomial_descFactorial_degree i)
      (fun i => polynomial_descFactorial_monic i)
  rw [← h2] at h1
  have : Matrix.det (Matrix.vandermonde fun i ↦ ↑(w' i)) = (Matrix.vandermonde v).det := by
    rw [det_vandermonde_eq_det_vandermonde_sub v m]
    congr
    unfold Matrix.vandermonde
    ext i j
    congr
    simp only [sub_nonneg]
    have : m ≤ v i  := by
      have v_in : (v i) ∈ (image v univ) := by
        unfold Finset.image
        simp only [Multiset.mem_toFinset, Multiset.mem_map, mem_val, mem_univ, true_and,
            exists_apply_eq_apply]
      have  v_in' : ↑(v i) ∈ toList (image v univ) := mem_toList.mpr v_in
      have h_min := h_min (v i) v_in'
      simp only [hm] at h_min
      rw [WithTop.some_eq_coe] at h_min
      norm_num at h_min
      exact h_min
    exact Int.toNat_sub_of_le this
  rw [this] at h1
  norm_num at h1
  use (Matrix.of (fun (i j : Fin (n + 1))  => ((Nat.choose ((v i  - m).toNat) (j : ℕ)) : ℤ))).det
  convert h1
  norm_cast

end Matrix
