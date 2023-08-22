/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li, Jujian Zhang
-/

import Mathlib.Order.KrullDimension
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Artinian
import Mathlib.Algebra.Module.LocalizedModule
import Mathlib.Topology.KrullDimension

/-!
# Krull dimension of a (commutative) ring

The ring theoretic krull dimension is the order theoretic krull dimension applied to its prime
spectrum. Unfolding this definition, it is the length of longest series of prime ideals ordered by
inclusion.

## Results
- `ringKrullDim.eq_of_ringEquiv` : isomorphic rings have equal krull dimension
- `primeIdealHeight_eq_ringKrullDim_of_Localization` : the height of a prime ideal `𝔭` is equal to
  krull dimension of `R_𝔭`
-/

/--
The ring theoretic Krull dimension is the Krull dimension of prime spectrum ordered by inclusion.
-/
noncomputable abbrev ringKrullDim (R : Type _) [CommRing R] : WithBot (WithTop ℕ) :=
  krullDim (PrimeSpectrum R)

namespace ringKrullDim

lemma eq_topologicalKrullDim (R : Type _) [CommRing R] :
  ringKrullDim R = topologicalKrullDim (PrimeSpectrum R) := by
refine' Eq.symm $ krullDim.eq_OrderDual.trans $ krullDim.eq_of_OrderIso $ OrderIso.symm {
  toFun := OrderDual.toDual ∘ λ p ↦ ⟨PrimeSpectrum.zeroLocus p.asIdeal,
    PrimeSpectrum.isClosed_zeroLocus p.asIdeal, (PrimeSpectrum.isIrreducible_zeroLocus_iff _).mpr
      $ by simpa only [p.IsPrime.radical] using p.IsPrime⟩
  invFun := (λ s ↦ ⟨PrimeSpectrum.vanishingIdeal s.1,
    PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.mp s.2.2⟩ :
      {s : Set (PrimeSpectrum R) | IsClosed s ∧ IsIrreducible s} → PrimeSpectrum R) ∘
        OrderDual.ofDual
  left_inv := λ p ↦ by
    ext1
    dsimp
    rw [PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, p.IsPrime.radical]
  right_inv := λ s ↦ by
    dsimp [OrderDual.ofDual]
    simp only [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, show
      closure (Subtype.val s) = Subtype.val s by exact s.2.1.closure_eq]
    exact rfl
  map_rel_iff' := by
    intro p q
    simp [PrimeSpectrum.zeroLocus_subset_zeroLocus_iff, q.IsPrime.radical] }

/--
If `R ⟶ S` is a surjective ring homomorphism, then `ringKrullDim S ≤ ringKrullDim R`.
-/
theorem le_of_surj (R S : Type _) [CommRing R] [CommRing S] (f : R →+* S)
  (hf : Function.Surjective f) : ringKrullDim S ≤ ringKrullDim R :=
krullDim.le_of_strictMono (PrimeSpectrum.comap f) (Monotone.strictMono_of_injective
  (λ _ _ hab ↦ Ideal.comap_mono hab) (PrimeSpectrum.comap_injective_of_surjective f hf))

/--
If `I` is an ideal of `R`, then `ringKrullDim (R ⧸ I) ≤ ringKrullDim R`.
-/
theorem le_of_quot (R : Type _) [CommRing R] (I : PrimeSpectrum R) :
  ringKrullDim (R ⧸ I.asIdeal) ≤ ringKrullDim R :=
le_of_surj _ _ (Ideal.Quotient.mk I.asIdeal) Ideal.Quotient.mk_surjective

/--
If `R` and `S` are isomorphic, then `ringKrullDim R = ringKrullDim S`.
-/
theorem eq_of_ringEquiv (R S : Type _) [CommRing R] [CommRing S] (e : R ≃+* S) :
  ringKrullDim R = ringKrullDim S :=
le_antisymm (le_of_surj S R (RingEquiv.symm e) (EquivLike.surjective (RingEquiv.symm e)))
  (le_of_surj R S e (EquivLike.surjective e))

instance primeSpectrum_unique_of_field (F : Type _) [Field F] : Unique (PrimeSpectrum F) where
  default := ⟨⊥, Ideal.bot_prime⟩
  uniq := λ p ↦ PrimeSpectrum.ext _ _ $ Ideal.ext $ λ x ↦ by
    refine ⟨λ h ↦ ?_, λ h ↦ h.symm ▸ Submodule.zero_mem _⟩
    rwa [p.asIdeal.eq_bot_of_prime] at h

instance finiteDimensionalType_of_field (F : Type _) [Field F] :
  FiniteDimensionalType (PrimeSpectrum F) := inferInstance

lemma eq_zero_of_Field (F : Type _) [Field F] : ringKrullDim F = 0 :=
  krullDim.eq_zero_of_unique

lemma eq_zero_of_isArtinianRing (R : Type _) [CommRing R] [Nontrivial R] [IsArtinianRing R] :
  ringKrullDim R = 0 := by
{ rw [ringKrullDim, krullDim.eq_iSup_height]
  suffices : ∀ (a : PrimeSpectrum R), height (PrimeSpectrum R) a = 0
  { simp_rw [this]; rw [iSup_const] }
  · intro p
    refine le_antisymm ?_ krullDim.nonneg_of_Nonempty
    · refine iSup_le (λ q ↦ ?_)
      · erw [WithBot.coe_le_coe, WithTop.coe_le_coe]
        by_contra' r
        have : q 0 < q 1 := by
          let hq := q.step ⟨0, r⟩
          rw [show (Fin.castSucc { val := 0, isLt := r }) = 0 by exact rfl,
            show (Fin.succ { val := 0, isLt := r }) = 1 by
            rw [show (Fin.succ { val := 0, isLt := r }) = 0 + 1 by
            exact Fin.ext $ Eq.symm (Fin.val_add_one_of_lt r)];
            exact Fin.zero_add 1] at hq
          exact hq
        haveI H0 : (q 0).1.asIdeal.IsMaximal := inferInstance
        exact (ne_of_lt this (show q 0 = q 1 by
          rw [Subtype.ext_iff_val, PrimeSpectrum.ext_iff];
          exact H0.eq_of_le (q 1).1.IsPrime.1 (le_of_lt this))) }

/--
Any PID that is not a field is finite dimensional with dimension 1.
-/
@[simps]
noncomputable def PID_finiteDimensional (R : Type _) [CommRing R] [IsPrincipalIdealRing R]
    [IsDomain R] (hR : ¬ IsField R) :
    FiniteDimensionalType (PrimeSpectrum R) where
  longestRelSeries := {
    toFun := (finTwoArrowEquiv $ PrimeSpectrum R).symm ⟨⟨⊥, Ideal.bot_prime⟩,
      ⟨(Ideal.exists_maximal R).choose, (Ideal.exists_maximal R).choose_spec.isPrime⟩⟩
    step := λ i ↦ by
      fin_cases i
      rw [show ⟨⊥, _⟩ = (⊥ : PrimeSpectrum R) by rfl]
      exact @Ideal.bot_lt_of_maximal R _ _ (Ideal.exists_maximal R).choose
        (Ideal.exists_maximal R).choose_spec hR }
  is_longest := λ x ↦ show x.length ≤ 1 from Decidable.by_contradiction $ λ rid ↦ by
    have m := LTSeries.strictMono x
    rcases x with ⟨l, f, s⟩
    rw [not_le] at rid
    let a := Submodule.IsPrincipal.generator (f 1).asIdeal
    let b := Submodule.IsPrincipal.generator (f 2).asIdeal
    have hf1 : (f 1).asIdeal ≠ ⊥ := λ h ↦ by
      have : (f 0).asIdeal < (f 1).asIdeal
      · rw [show 0 = Fin.castSucc ⟨0, Nat.lt_of_succ_lt rid⟩ by rfl, show 1 = Fin.succ
          ⟨0, Nat.lt_of_succ_lt rid⟩ from ?_]
        · exact s ⟨0, Nat.lt_of_succ_lt rid⟩
        · ext; change 1 % (l + 1) = 1; rw [Nat.mod_eq_of_lt]; linarith
      rw [h] at this
      exact (not_le_of_lt this bot_le).elim
    have hf12 : (f 1).asIdeal < (f 2).asIdeal := by
      rw [show 1 = Fin.castSucc ⟨1, rid⟩ from ?_, show 2 = Fin.succ ⟨1, rid⟩ from ?_]
      · exact s ⟨1, rid⟩
      · ext; change 2 % (l + 1) = 2; rw [Nat.mod_eq_of_lt]; linarith
      · ext; change 1 % (l + 1) = 1; rw [Nat.mod_eq_of_lt]; linarith
    have lt1 : Ideal.span {a} < Ideal.span {b} := by
      rw [Ideal.span_singleton_generator, Ideal.span_singleton_generator]
      exact hf12
    rw [Ideal.span_singleton_lt_span_singleton] at lt1
    rcases lt1 with ⟨h, ⟨r, hr1, hr2⟩⟩
    have ha : Prime a := Submodule.IsPrincipal.prime_generator_of_isPrime (f 1).asIdeal hf1
    have hb : Prime b := Submodule.IsPrincipal.prime_generator_of_isPrime (f 2).asIdeal $
      Iff.mp bot_lt_iff_ne_bot (lt_trans (Ne.bot_lt hf1) hf12)
    · obtain ⟨x, hx⟩ := (hb.dvd_prime_iff_associated ha).mp ⟨r, hr2⟩
      rw [←hx] at hr2
      rw [←mul_left_cancel₀ h hr2] at hr1
      exact (hr1 x.isUnit).elim

lemma PID_eq_one_of_not_isField (R : Type _) [CommRing R] [IsPrincipalIdealRing R] [IsDomain R]
    (hR : ¬ IsField R) : ringKrullDim R = 1 := by
  rw [ringKrullDim, @krullDim.eq_len_of_finiteDimensionalType _ _ (PID_finiteDimensional _ hR)]; rfl

/--
https://stacks.math.columbia.edu/tag/00KG
-/
lemma eq_iSup_height_maximal_ideals (R : Type _) [CommRing R] : ringKrullDim R =
  ⨆ (p : PrimeSpectrum R) (_ : p.asIdeal.IsMaximal), height (PrimeSpectrum R) p := by
refine' krullDim.eq_iSup_height.trans $ le_antisymm ?_ ?_
· exact iSup_le $ λ p ↦ by
    rcases (p.asIdeal.exists_le_maximal p.IsPrime.1) with ⟨q, ⟨h1, h2⟩⟩
    refine' le_trans ?_ (le_sSup ⟨⟨q, Ideal.IsMaximal.isPrime h1⟩, iSup_pos h1⟩)
    exact krullDim.height_mono h2
· rw [show (⨆ (a : PrimeSpectrum R), height (PrimeSpectrum R) a) = ⨆ (a : PrimeSpectrum R)
    (_ : true), height (PrimeSpectrum R) a by simp only [iSup_pos]]
  exact iSup_le_iSup_of_subset $ λ _ _ ↦ rfl

/-
Here we aim to show that for any prime ideal `I` of a commutative ring `R`, the
height of `I` equals the Krull dimension of `Localization.AtPrime I.asIdeal`.
-/
section aboutHeightAndLocalization

variable {R : Type _} [CommRing R] (J : Ideal R) (I : PrimeSpectrum R)

/--
For any ideal `J` and submonoid `x` of `R`, `Ideal.localization J x` is
the ideal `J.map (algebraMap R (Localization x))` of `Localization x`.
-/
abbrev _root_.Ideal.localization (x : Submonoid R) : Ideal (Localization x) :=
  J.map (algebraMap R (Localization x))

/--
For any ideals `J` and `I` of `R` such that `I` is prime, `Ideal.localizationAtPrime J I`
is defined as `J.localization I.asIdeal.primeCompl`.
-/
abbrev _root_.Ideal.localizationAtPrime := J.localization I.asIdeal.primeCompl

/-- The canonical map from the ideal J of R to its image JR_I in the localisation. -/
@[simps apply] def _root_.Ideal.toLocalization (x : Submonoid R) :
  J →ₗ[R] J.localization x where
  toFun := λ x ↦ ⟨Localization.mk x 1, Submodule.subset_span ⟨_, x.2, rfl⟩⟩
  map_add' := λ _ _ ↦ Subtype.ext (Localization.add_mk_self _ _ _).symm
  map_smul' := λ _ _ ↦ Subtype.ext (Localization.smul_mk _ _ _).symm

/--
For any ideal `J` and submonoid `y` of `R`, `Ideal.localization' J y` is defined
as the collection of all elements which can be written as `Localization.mk ↑a b`
for some `a : J` and `b : y`.
-/
@[simps!]
def _root_.Ideal.localization' (y : Submonoid R) : Ideal (Localization y) where
  carrier := { x | ∃ (a : J) (b : y), x = Localization.mk ↑a b }
  add_mem' := fun {x y} ⟨a1, ⟨b1, hx⟩⟩ ⟨a2, ⟨b2, hy⟩⟩ => hx.symm ▸ hy.symm ▸
    ⟨⟨_, J.add_mem (J.mul_mem_left b1 (SetLike.coe_mem a2))
      (J.mul_mem_left b2 (SetLike.coe_mem a1))⟩, ⟨b1 * b2, Localization.add_mk _ _ _ _⟩⟩
  zero_mem' := ⟨0, ⟨1, by
    simp only [Localization.mk_eq_monoidOf_mk']
    rw [Submonoid.LocalizationMap.mk']
    simp only [map_one, inv_one, Units.val_one, mul_one]
    exact Eq.symm (Localization.mk_zero 1)⟩⟩
  smul_mem' := λ c ↦ Localization.induction_on c $ by
    rintro ⟨c1, c2⟩ ⟨j, ⟨a, rfl⟩⟩
    exact ⟨⟨_, J.mul_mem_left c1 (SetLike.coe_mem j)⟩, ⟨c2 * a, Localization.mk_mul _ _ _ _⟩⟩

lemma _root_.Ideal.mem_localization'_iff {y : Submonoid R} (x : Localization y) :
  x ∈ J.localization' y ↔ ∃ (a : J) (b : y), x = Localization.mk ↑a b :=
Iff.rfl

lemma _root_.Ideal.mem_localization'_of_mem_localization (y : Submonoid R) :
    ∀ x, x ∈ J.localization y → x ∈ J.localization' y := by
  intro x hx
  apply Submodule.span_induction' ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨y, hy1, rfl⟩; refine ⟨⟨y, hy1⟩, ⟨_, rfl⟩⟩
  · exact Ideal.zero_mem _
  · intro _ _ _ _; apply Ideal.add_mem
  · intro a _ _; exact Submodule.smul_mem _ a

lemma _root_.Ideal.localization'_eq_localization (y : Submonoid R) :
    J.localization' y = J.localization y :=
  le_antisymm (by
    rintro x ⟨⟨a, ha⟩, ⟨b, rfl⟩⟩
    rw [Subtype.coe_mk, ←one_mul a, ←mul_one b, ←Localization.mk_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ ha)) <|
  J.mem_localization'_of_mem_localization _

instance _root_.Ideal.localization'_IsPrime (J : Set.Iic I) :
  (J.1.asIdeal.localization' I.asIdeal.primeCompl).IsPrime where
ne_top' := fun hit => by
  rw [Ideal.eq_top_iff_one] at hit
  rcases hit with ⟨a, ⟨b, hb⟩⟩
  exact (IsLocalization.AtPrime.isUnit_mk'_iff (Localization.AtPrime I.asIdeal) _
    (a : R) b).mp (by simpa only [←Localization.mk_eq_mk', ←hb] using isUnit_one) (J.2 a.2)
mem_or_mem' := by
    intro x y
    refine Localization.induction_on₂ x y ?_
    rintro ⟨a1, a2⟩ ⟨b1, b2⟩ ⟨⟨p, hp⟩, ⟨q, h⟩⟩
    rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists] at h
    obtain ⟨c, hc⟩ := h
    have h : ↑c * (↑q * (a1 * b1)) ∈ J.1.asIdeal := hc.symm ▸ J.1.asIdeal.mul_mem_left _
      (J.1.asIdeal.mul_mem_left _ hp)
    rw [←mul_assoc] at h
    exact (J.1.IsPrime.mem_or_mem ((J.1.IsPrime.mem_or_mem h).resolve_left
      (fun h => Submonoid.mul_mem _ c.2 q.2 (J.2 h)))).elim
        (fun h => Or.intro_left _ ⟨⟨a1, h⟩, ⟨_, rfl⟩⟩)
        (fun h => Or.intro_right _ ⟨⟨b1, h⟩, ⟨_, rfl⟩⟩)

/--
There is a canonical map from `Set.Iic I` to `PrimeSpectrum (Localization.AtPrime I.asIdeal)`.
-/
def _root_.PrimeSpectrum.IicToLocalizationAtPrime :
  Set.Iic I → PrimeSpectrum (Localization.AtPrime I.asIdeal) :=
λ I' ↦ ⟨I'.1.asIdeal.localization' I.asIdeal.primeCompl, inferInstance⟩

/--
There is a canonical map from `PrimeSpectrum (Localization.AtPrime I.asIdeal)` to `Set.Iic I`.
-/
@[simp]
 def _root_.PrimeSpectrum.LocalizationAtPrimeToIic :
   PrimeSpectrum (Localization.AtPrime I.asIdeal) → Set.Iic I :=
   λ J ↦ ⟨⟨_, Ideal.IsPrime.comap (hK := J.2) (algebraMap R (Localization.AtPrime I.asIdeal))⟩,
     λ z hz ↦
     @Decidable.byContradiction _ (Classical.dec _) $ λ hnz ↦ J.IsPrime.ne_top $ eq_top_iff.mpr $
     False.elim $ J.IsPrime.1 $ (Ideal.eq_top_iff_one _).mpr <| show 1 ∈ J.asIdeal by
       rw [show (1 : Localization.AtPrime I.asIdeal) = Localization.mk z 1 * Localization.mk 1
         (⟨z, hnz⟩ : I.asIdeal.primeCompl) by simpa only
           [Localization.mk_one_eq_algebraMap, ←Algebra.smul_def, Localization.smul_mk, smul_eq_mul,
             mul_one, eq_comm] using Localization.mk_self (⟨z, hnz⟩ : I.asIdeal.primeCompl)]
       exact Ideal.mul_mem_right _ _ hz⟩

/--
The canonical map from `PrimeSpectrum (Localization.AtPrime I.asIdeal)` to `Set.Iic I` is a left
inverse to the canonical map from `Set.Iic I` to `PrimeSpectrum (Localization.AtPrime I.asIdeal)`.
-/
lemma _root_.PrimeSpectrum.LocalizationAtPrimeToIic_IsLeftInverse :
  Function.LeftInverse (PrimeSpectrum.LocalizationAtPrimeToIic I)
    (PrimeSpectrum.IicToLocalizationAtPrime I) := by
{ intro J; ext x; constructor
  · intro hx
    change Localization.mk x 1 ∈ _root_.Ideal.localization' J.val.asIdeal I.asIdeal.primeCompl at hx
    rcases hx with ⟨a, b, hab⟩
    erw [Localization.mk_eq_mk_iff, Localization.r_iff_exists, one_mul] at hab
    rcases hab with ⟨c, hc⟩
    rw [←mul_assoc] at hc
    exact (or_iff_not_imp_left.1 (Ideal.IsPrime.mem_or_mem J.val.2 (@Set.mem_of_eq_of_mem R
      (↑c * ↑b * x) (↑c * ↑a) J.val.asIdeal hc (Ideal.mul_mem_left J.val.asIdeal ↑c a.2))))
        (λ hi ↦ (Submonoid.mul_mem I.asIdeal.primeCompl c.2 b.2) (J.2 hi))
  · intro hx
    exact ⟨⟨x, hx⟩, ⟨1, rfl⟩⟩ }

/--
The canonical map from `PrimeSpectrum (Localization.AtPrime I.asIdeal)` to `Set.Iic I` is a right
inverse to the canonical map from `Set.Iic I` to `PrimeSpectrum (Localization.AtPrime I.asIdeal)`.
-/
lemma _root_.PrimeSpectrum.LocalizationAtPrimeToIic_IsRightInverse :
  Function.RightInverse (PrimeSpectrum.LocalizationAtPrimeToIic I)
    (PrimeSpectrum.IicToLocalizationAtPrime I) := by
{ intro J; ext x; constructor
  · intro hx
    rcases hx with ⟨⟨a, ha⟩, ⟨b, hab⟩⟩
    dsimp at ha hab
    rw [←one_mul a, ←mul_one b, ←Localization.mk_mul] at hab; rw [hab]
    exact Ideal.mul_mem_left J.asIdeal (Localization.mk 1 b) ha
  · refine Localization.induction_on x ?_
    · rintro ⟨a, b⟩ hab
      refine' ⟨⟨a, ?_⟩, b, rfl⟩
      · change Localization.mk a 1 ∈ J.asIdeal
        rw [←show (Localization.mk (b : R) 1) * (Localization.mk a b) = Localization.mk a 1 by
          rw [Localization.mk_mul, mul_comm, ←Localization.mk_mul, Localization.mk_self, mul_one]]
        exact Ideal.mul_mem_left J.asIdeal (Localization.mk b 1) hab }

/--
The canonical map from `Set.Iic I` to `PrimeSpectrum (Localization.AtPrime I.asIdeal)`
is bijective (not necessary for the proof).
-/
lemma _root_.PrimeSpectrum.IicToLocalizationAtPrime.bijective :
  Function.Bijective (PrimeSpectrum.IicToLocalizationAtPrime I) := by
rw [Function.bijective_iff_has_inverse]
exact ⟨PrimeSpectrum.LocalizationAtPrimeToIic I,
  ⟨PrimeSpectrum.LocalizationAtPrimeToIic_IsLeftInverse I,
    PrimeSpectrum.LocalizationAtPrimeToIic_IsRightInverse I⟩⟩

/--
The canonical map from `PrimeSpectrum (Localization.AtPrime I.asIdeal)` to `Set.Iic I`
is bijective (not necessary for the proof).
-/
lemma _root_.PrimeSpectrum.LocalizationAtPrimeToIic.bijective :
  Function.Bijective (PrimeSpectrum.LocalizationAtPrimeToIic I) := by
rw [Function.bijective_iff_has_inverse]
exact ⟨PrimeSpectrum.IicToLocalizationAtPrime I,
  ⟨PrimeSpectrum.LocalizationAtPrimeToIic_IsRightInverse I,
    PrimeSpectrum.LocalizationAtPrimeToIic_IsLeftInverse I⟩⟩

/--
The canonical map from `Set.Iic I` to `PrimeSpectrum (Localization.AtPrime I.asIdeal)`
is monotone.
-/
lemma _root_.PrimeSpectrum.IicToLocalizationAtPrime_isMonotone :
  Monotone (PrimeSpectrum.IicToLocalizationAtPrime I) := by
{ intro J1 J2 H x hx; rcases hx with ⟨a, ⟨b, hab⟩⟩; exact ⟨⟨a, H a.2⟩, ⟨b, hab⟩⟩ }

/--
The canonical map from `PrimeSpectrum (Localization.AtPrime I.asIdeal)` to `Set.Iic I`
is monotone.
-/
lemma _root_.PrimeSpectrum.LocalizationAtPrimeToIic_isMonotone :
  Monotone (PrimeSpectrum.LocalizationAtPrimeToIic I) := by
{ intro J1 J2 H x hx; exact H hx }

/--
We can regard the canonical map from `Set.Iic I` to `PrimeSpectrum (Localization.AtPrime I.asIdeal)`
as an equivalence.
-/
def _root_.PrimeSpectrum.IicToLocalizationAtPrimeEquiv :
  (Set.Iic I) ≃ (PrimeSpectrum (Localization.AtPrime I.asIdeal)) where
    toFun := PrimeSpectrum.IicToLocalizationAtPrime I
    invFun := PrimeSpectrum.LocalizationAtPrimeToIic I
    left_inv := PrimeSpectrum.LocalizationAtPrimeToIic_IsLeftInverse I
    right_inv := PrimeSpectrum.LocalizationAtPrimeToIic_IsRightInverse I

/--
We can regard the canonical map from `PrimeSpectrum (Localization.AtPrime I.asIdeal)` to
`Set.Iic I` as an equivalence.
-/
def _root_.PrimeSpectrum.LocalizationAtPrimeToIicEquiv :
  (PrimeSpectrum (Localization.AtPrime I.asIdeal)) ≃ (Set.Iic I) where
    toFun := PrimeSpectrum.LocalizationAtPrimeToIic I
    invFun := PrimeSpectrum.IicToLocalizationAtPrime I
    left_inv := PrimeSpectrum.LocalizationAtPrimeToIic_IsRightInverse I
    right_inv := PrimeSpectrum.LocalizationAtPrimeToIic_IsLeftInverse I

lemma _root_.PrimeSpectrum.IicToLocalizationAtPrimeEquiv_IsMonotone :
  Monotone (PrimeSpectrum.IicToLocalizationAtPrimeEquiv I) := by
{ exact PrimeSpectrum.IicToLocalizationAtPrime_isMonotone I }

lemma _root_.PrimeSpectrum.LocalizationAtPrimeToIicEquiv_IsMonotone :
  Monotone (PrimeSpectrum.LocalizationAtPrimeToIicEquiv I) := by
{ exact PrimeSpectrum.LocalizationAtPrimeToIic_isMonotone I }

lemma _root_.PrimeSpectrum.LocalizationAtPrimeToIicEquiv_is_symm :
  PrimeSpectrum.LocalizationAtPrimeToIicEquiv I =
    (PrimeSpectrum.IicToLocalizationAtPrimeEquiv I).symm := rfl

/--
We have a canonical order isomorphism from `Set.Iic I` to
`PrimeSpectrum (Localization.AtPrime I.asIdeal)`.
-/
@[simp]
def _root_.PrimeSpectrum.IicToLocalizationAtPrime_OrderIso :
  (Set.Iic I) ≃o (PrimeSpectrum (Localization.AtPrime I.asIdeal)) := by
exact Equiv.toOrderIso (PrimeSpectrum.IicToLocalizationAtPrimeEquiv I)
  (PrimeSpectrum.IicToLocalizationAtPrimeEquiv_IsMonotone I)
    (PrimeSpectrum.LocalizationAtPrimeToIicEquiv_IsMonotone I)

/--
The height of `I` is equal to the Krull dimension of `localization.at_prime I.as_ideal`.
-/
theorem primeIdealHeight_eq_ringKrullDim_of_Localization :
  height (PrimeSpectrum R) I = ringKrullDim (Localization.AtPrime I.asIdeal) :=
krullDim.eq_of_OrderIso (PrimeSpectrum.IicToLocalizationAtPrime_OrderIso I)

end aboutHeightAndLocalization

end ringKrullDim