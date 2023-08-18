/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Pi
import Mathlib.Algebra.CharP.Quotient
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.MvPolynomial.CommRing
import Mathlib.Data.Nat.Prime
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.MvPolynomial
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.Finsupp
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal

/-! # `algebraMap R (CliffordAlgebra Q)` is not always injective.

A formalization of https://mathoverflow.net/questions/60596/clifford-pbw-theorem-for-quadratic-form/87958#87958

Some Zulip discussion at https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/.F0.9D.94.BD.E2.82.82.5B.CE.B1.2C.20.CE.B2.2C.20.CE.B3.5D.20.2F.20.28.CE.B1.C2.B2.2C.20.CE.B2.C2.B2.2C.20.CE.B3.C2.B2.29/near/222716333.
-/


noncomputable section

open scoped BigOperators

section ForMathlib

theorem Ideal.comap_span_le {R : Type _} {S : Type _} [Semiring R] [Semiring S] (f : S →+* R)
    (g : R →+* S) (h : Function.LeftInverse g f) (s : Set R) :
    Ideal.comap f (Ideal.span s) ≤ Ideal.span (g '' s) := by
  rintro x (hx : f x ∈ Ideal.span s)
  have := Ideal.apply_coe_mem_map g _ ⟨_, hx⟩
  rw [Ideal.map_span, Subtype.coe_mk, h x] at this
  exact this

/-- `char_p.quotient'` as an `iff`. -/
theorem CharP.quotient_iff' (R : Type _) [CommRing R] (n : ℕ) [CharP R n] (I : Ideal R) :
    CharP (R ⧸ I) n ↔ ∀ x : ℕ, ↑x ∈ I → (x : R) = 0 := by
  refine' ⟨fun (i : CharP (R ⧸ I) n) x hx => _, CharP.quotient' n I⟩
  skip
  have := CharP.cast_eq_zero_iff (R ⧸ I) n
  rw [CharP.cast_eq_zero_iff R n]
  refine' (this _).mp _
  exact (Submodule.Quotient.mk_eq_zero I).mpr hx

theorem Ideal.span_le_bot {R : Type _} [Semiring R] (s : Set R) : Ideal.span s ≤ ⊥ ↔ s ≤ {0} :=
  Submodule.span_le

/-- `char_p.quotient'` as an `iff`. -/
theorem CharP.quotient_iff'' (R : Type _) [CommRing R] (n : ℕ) [CharP R n] (I : Ideal R) :
    CharP (R ⧸ I) n ↔ I.comap (Nat.castRingHom R) ≤ RingHom.ker (Nat.castRingHom R) :=
  (CharP.quotient_iff' _ _ _).trans
    (by
      rw [RingHom.ker_eq_comap_bot]
      exact Iff.rfl)

theorem Finsupp.equivFunOnFinite_const {α β} [Fintype α] [AddCommMonoid β] (b : β) :
    Finsupp.equivFunOnFinite.symm (fun _ => b : α → β) = ∑ i : α, Finsupp.single i b := by
  ext; simp [Finsupp.finset_sum_apply]

nonrec theorem Ideal.mem_span_range_iff_exists_fun {ι R} [Fintype ι] [CommSemiring R]
    (g : ι → R) (x : R) :
    x ∈ Ideal.span (Set.range g) ↔ ∃ f : ι → R, ∑ i, f i * g i = x :=
  mem_span_range_iff_exists_fun _

end ForMathlib

namespace Q60596

open MvPolynomial

/-- The monomial ideal generated by terms of the form $x_ix_i$. -/
def kIdeal : Ideal (MvPolynomial (Fin 3) (ZMod 2)) :=
  Ideal.span (Set.range fun i => (X i * X i : MvPolynomial (Fin 3) (ZMod 2)))

theorem mem_kIdeal_iff (x : MvPolynomial (Fin 3) (ZMod 2)) :
    x ∈ kIdeal ↔ ∀ m : Fin 3 →₀ ℕ, m ∈ x.support → ∃ i, 2 ≤ m i := by
  have :
      kIdeal =
        Ideal.span ((monomial (R := ZMod 2) · (1 : ZMod 2)) '' Set.range (Finsupp.single · 2)) :=
    by simp_rw [kIdeal, X, monomial_mul, one_mul, ← Finsupp.single_add, ← Set.range_comp,
      Function.comp]
  rw [this, mem_ideal_span_monomial_image]
  simp

theorem X0_X1_X2_nmem_kIdeal : (X 0 * X 1 * X 2 : MvPolynomial (Fin 3) (ZMod 2)) ∉ kIdeal := by
  intro h
  simp_rw [mem_kIdeal_iff, support_mul_X, support_X, Finset.map_singleton, addRightEmbedding_apply,
    Finset.mem_singleton, forall_eq, ← Fin.sum_univ_three fun i => Finsupp.single i 1, ←
    Finsupp.equivFunOnFinite_const] at h

theorem mul_self_mem_kIdeal_of_X0_X1_X2_mul_mem {x : MvPolynomial (Fin 3) (ZMod 2)}
    (h : X 0 * X 1 * X 2 * x ∈ kIdeal) : x * x ∈ kIdeal := by
  rw [mem_kIdeal_iff] at h
  have : x ∈ Ideal.span ((X : Fin 3 → MvPolynomial _ (ZMod 2)) '' Set.univ) := by
    rw [mem_ideal_span_X_image]
    intro m hm
    simp_rw [mul_assoc, support_X_mul, Finset.map_map, Finset.mem_map,
      Function.Embedding.trans_apply, addLeftEmbedding_apply, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂, ← add_assoc, ←
      Fin.sum_univ_three fun i => Finsupp.single i 1, ← Finsupp.equivFunOnFinite_const,
      Finsupp.add_apply, Finsupp.equivFunOnFinite_symm_apply_toFun] at h
    refine' (h _ hm).imp fun i hi => ⟨Set.mem_univ _, _⟩
    rintro hmi
    rw [hmi] at hi
    norm_num at hi
  rw [as_sum x, CharTwo.sum_mul_self]
  refine' sum_mem fun m hm => _
  rw [mem_kIdeal_iff, monomial_mul]
  intro m' hm'
  obtain rfl := Finset.mem_singleton.1 (support_monomial_subset hm')
  rw [mem_ideal_span_X_image] at this
  obtain ⟨i, _, hi⟩ := this m hm
  simp_rw [←one_add_one_eq_two]
  refine' ⟨i, Nat.add_le_add _ _⟩ <;> rwa [Nat.one_le_iff_ne_zero]

-- 𝔽₂[α, β, γ] / (α², β², γ²)
def K : Type _ :=
  _ ⧸ kIdeal

instance : CommRing K := by dsimp only [K]; infer_instance
instance : CommSemiring K := by dsimp only [K]; infer_instance
instance : Ring K := by dsimp only [K]; infer_instance
instance : Semiring K := by dsimp only [K]; infer_instance
instance : AddCommGroup K := by dsimp only [K]; infer_instance
instance : AddCommMonoid K := by dsimp only [K]; infer_instance

theorem comap_C_span_le_bot : kIdeal.comap (C : ZMod 2 →+* MvPolynomial (Fin 3) (ZMod 2)) ≤ ⊥ := by
  refine' (Ideal.comap_span_le _ _ (constantCoeff_C _) _).trans _
  refine' (Ideal.span_le_bot _).2 _
  rintro x ⟨_, ⟨i, rfl⟩, rfl⟩
  rw [RingHom.map_mul, constantCoeff_X, MulZeroClass.mul_zero, Set.mem_singleton_iff]

/-- `k` has characteristic 2. -/
instance K.charP : CharP K 2 := by
  dsimp only [K]
  rw [CharP.quotient_iff'']
  have : Nat.castRingHom (MvPolynomial (Fin 3) (ZMod 2)) = C.comp (Nat.castRingHom _) := by
    ext1 r; rfl
  rw [this, ← Ideal.comap_comap, ← RingHom.comap_ker]
  exact Ideal.comap_mono (comap_C_span_le_bot.trans bot_le)

abbrev α : K :=
  Ideal.Quotient.mk _ (MvPolynomial.X 0)

abbrev β : K :=
  Ideal.Quotient.mk _ (MvPolynomial.X 1)

abbrev γ : K :=
  Ideal.Quotient.mk _ (MvPolynomial.X 2)

/-- The elements above square to zero -/
@[simp]
theorem X_sq (i : Fin 3) :
    Ideal.Quotient.mk _ (MvPolynomial.X i) * Ideal.Quotient.mk _ (MvPolynomial.X i) = (0 : K) := by
  change Ideal.Quotient.mk _ _ = _
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨i, rfl⟩

-- rw can use `X_sq`, but `simp` needs these specializations
@[simp] theorem α_sq : α * α = 0 := X_sq _
@[simp] theorem β_sq : β * β = 0 := X_sq _
@[simp] theorem γ_sq : γ * γ = 0 := X_sq _

/-- If an element multiplied by `αβγ` is zero then it squares to zero. -/
theorem sq_zero_of_αβγ_mul {x : K} : α * β * γ * x = 0 → x * x = 0 := by
  induction x using Quotient.inductionOn'
  change Ideal.Quotient.mk _ _ = 0 → Ideal.Quotient.mk _ _ = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.eq_zero_iff_mem]
  exact mul_self_mem_kIdeal_of_X0_X1_X2_mul_mem

/-- Though `αβγ` is not itself zero-/
theorem αβγ_ne_zero : α * β * γ ≠ 0 := fun h =>
  X0_X1_X2_nmem_kIdeal <| Ideal.Quotient.eq_zero_iff_mem.1 h

local macro_rules | `($x • $y) => `(@HSMul.hSMul _ _ _ instHSMul $x $y) -- Porting note: See issue lean4#2220

@[simps!]
def lFunc : (Fin 3 → K) →ₗ[K] K :=
  letI proj : Fin 3 → (Fin 3 → K) →ₗ[K] K := LinearMap.proj
  α • proj 0 - β • proj 1 - γ • proj 2

/-- The quotient of k^3 by the specified relation-/
abbrev L : Type _ :=  _ ⧸ LinearMap.ker lFunc

def sq {ι R : Type _} [CommRing R] (i : ι) : QuadraticForm R (ι → R) :=
  QuadraticForm.sq.comp <| LinearMap.proj i

theorem sq_map_add_char_two {ι R : Type _} [CommRing R] [CharP R 2] (i : ι) (a b : ι → R) :
    sq i (a + b) = sq i a + sq i b :=
  CharTwo.add_mul_self _ _

theorem sq_map_sub_char_two {ι R : Type _} [CommRing R] [CharP R 2] (i : ι) (a b : ι → R) :
    sq i (a - b) = sq i a - sq i b := by
  haveI : Nonempty ι := ⟨i⟩
  rw [CharTwo.sub_eq_add, CharTwo.sub_eq_add, sq_map_add_char_two]

open scoped BigOperators

/-- The quadratic form (metric) is just euclidean -/
def Q' : QuadraticForm K (Fin 3 → K) :=
  ∑ i, sq i

theorem Q'_add (x y : Fin 3 → K) : Q' (x + y) = Q' x + Q' y := by
  simp only [Q', (QuadraticForm.sum_apply), (sq_map_add_char_two), (Finset.sum_add_distrib)]

theorem Q'_sub (x y : Fin 3 → K) : Q' (x - y) = Q' x - Q' y := by
  simp only [Q', (QuadraticForm.sum_apply), (sq_map_sub_char_two), (Finset.sum_sub_distrib)]

theorem Q'_apply (a : Fin 3 → K) : Q' a = a 0 * a 0 + a 1 * a 1 + a 2 * a 2 :=
  calc
    Q' a = a 0 * a 0 + (a 1 * a 1 + (a 2 * a 2 + 0)) := rfl
    _ = _ := by ring

theorem Q'_apply_single (i : Fin 3) (x : K) : Q' (Pi.single i x) = x * x :=
  calc
    Q' (Pi.single i x) = ∑ j : Fin 3, (Pi.single i x * Pi.single i x : Fin 3 → K) j := by
      simp [Q', sq, (QuadraticForm.sum_apply), (QuadraticForm.comp_apply),
        (QuadraticForm.sq_apply), (LinearMap.proj_apply)]
    _ = _ := by simp_rw [← Pi.single_mul, Finset.sum_pi_single', Finset.mem_univ, if_pos]

theorem Q'_zero_under_ideal (v : Fin 3 → K) (hv : v ∈ LinearMap.ker lFunc) : Q' v = 0 := by
  rw [LinearMap.mem_ker, lFunc_apply] at hv
  have h0 : α * β * γ * v 0 = 0 := by
    have := congr_arg ((· * ·) (β * γ)) hv
    simp only [MulZeroClass.mul_zero, mul_add, ← mul_assoc] at this
    rw [mul_comm (β * γ) α, ← mul_assoc, mul_right_comm β γ β, mul_assoc β γ γ, X_sq, X_sq] at this
    simpa only [MulZeroClass.mul_zero, MulZeroClass.zero_mul, add_zero, zero_add] using this
  have h1 : α * β * γ * v 1 = 0 := by
    have := congr_arg ((· * ·) (α * γ)) hv
    simp only [MulZeroClass.mul_zero, mul_add, ← mul_assoc] at this
    rw [mul_right_comm α γ α, mul_assoc α γ γ, mul_right_comm α γ β, X_sq, X_sq] at this
    simpa only [MulZeroClass.mul_zero, MulZeroClass.zero_mul, add_zero, zero_add] using this
  have h2 : α * β * γ * v 2 = 0 := by
    have := congr_arg ((· * ·) (α * β)) hv
    simp only [MulZeroClass.mul_zero, mul_add, ← mul_assoc] at this
    rw [mul_right_comm α β α, mul_assoc α β β, X_sq, X_sq] at this
    simpa only [MulZeroClass.mul_zero, MulZeroClass.zero_mul, add_zero, zero_add] using this
  rw [Q'_apply, sq_zero_of_αβγ_mul h0, sq_zero_of_αβγ_mul h1, sq_zero_of_αβγ_mul h2, add_zero,
    add_zero]

/-- `Q'`, lifted to operate on the quotient space `L`. -/
@[simps!]
def Q : QuadraticForm K L :=
  QuadraticForm.ofPolar
    (fun x =>
      Quotient.liftOn' x Q' fun a b h => by
        rw [Submodule.quotientRel_r_def] at h
        suffices Q' (a - b) = 0 by rwa [Q'_sub, sub_eq_zero] at this
        apply Q'_zero_under_ideal (a - b) h)
    (fun a x => by
      induction x using Quotient.inductionOn
      exact Q'.toFun_smul a _)
    (by rintro ⟨x⟩ ⟨x'⟩ ⟨y⟩; exact Q'.polar_add_left x x' y)
    (by rintro c ⟨x⟩ ⟨y⟩; exact Q'.polar_smul_left c x y)

open CliffordAlgebra

/-! Shorthand for basis vectors in the Clifford algebra -/

abbrev x' : CliffordAlgebra Q := ι Q <| Submodule.Quotient.mk (Pi.single 0 1)
abbrev y' : CliffordAlgebra Q := ι Q <| Submodule.Quotient.mk (Pi.single 1 1)
abbrev z' : CliffordAlgebra Q := ι Q <| Submodule.Quotient.mk (Pi.single 2 1)

/-- The basis vectors square to one -/
@[simp]
theorem x_mul_x : x' * x' = 1 := by
  dsimp only [x']
  simp_rw [CliffordAlgebra.ι_sq_scalar, Q_apply, ← Submodule.Quotient.mk''_eq_mk,
    Quotient.liftOn'_mk'', Q'_apply_single, mul_one, map_one]

/-- By virtue of the quotient, terms of this form are zero -/
theorem quot_obv : α • x' - β • y' - γ • z' = 0 := by
  dsimp only [x', y', z']
  simp only [← (LinearMap.map_smul), ← (LinearMap.map_sub), ← Submodule.Quotient.mk_smul, ←
    Submodule.Quotient.mk_sub]
  convert LinearMap.map_zero _ using 2
  rw [Submodule.Quotient.mk_eq_zero]
  norm_num [sub_zero, Ideal.span, Pi.single_apply]

set_option maxHeartbeats 400000 in
/-- The core of the proof - scaling `1` by `α * β * γ` gives zero -/
theorem αβγ_smul_eq_zero : (α * β * γ) • (1 : CliffordAlgebra Q) = 0 :=
  by
  suffices α • 1 - β • (y' * x') - γ • (z' * x') = 0
    by
    have := congr_arg (fun x => (β * γ) • x) this
    dsimp only at this
    simp_rw [smul_sub, smul_smul] at this
    rwa [mul_assoc β γ γ, mul_right_comm β γ β, mul_right_comm β γ α, mul_comm β α, X_sq, X_sq, zero_mul, mul_zero,
      zero_smul, zero_smul, sub_zero, sub_zero, smul_zero] at this
  have : (α • x' - β • y' - γ • z') * x' = α • 1 - β • (y' * x') - γ • (z' * x') := by
    simp_rw [sub_mul, smul_mul_assoc, x_mul_x]
  rw [← this]
  rw [quot_obv, MulZeroClass.zero_mul]

/-- Our final result -/
theorem algebraMap_not_injective : ¬Function.Injective (algebraMap K <| CliffordAlgebra Q) :=
  fun h => αβγ_ne_zero <| h <| by
    rw [Algebra.algebraMap_eq_smul_one, RingHom.map_zero, αβγ_smul_eq_zero]

end Q60596

open Q60596 in
/-- The general statement: not every Clifford algebra over a module has an injective algebra map. -/
theorem CliffordAlgebra.not_forall_algebraMap_injective.{v} :
    -- TODO: make `R` universe polymorphic
    ¬∀ (R : Type) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] (Q : QuadraticForm R M),
      Function.Injective (algebraMap R <| CliffordAlgebra Q) :=
  fun h => algebraMap_not_injective fun x y hxy => by
    let uU := ULift.moduleEquiv (R := K) (M := L)
    let uQ := Q.comp uU.toLinearMap
    refine' h K (ULift L) (Q.comp uU.toLinearMap) _
    let uC := CliffordAlgebra.map Q uQ uU.symm.toLinearMap fun _ => rfl
    have := uC.congr_arg hxy
    rwa [AlgHom.commutes, AlgHom.commutes] at this
