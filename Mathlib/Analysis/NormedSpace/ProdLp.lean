/-
Copyright (c) 2023 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Sébastien Gouëzel, Jireh Loreaux
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fintype.Order
import Mathlib.LinearAlgebra.Matrix.Basis

local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y) -- Porting note: See issue #2220

open Real Set Filter IsROrC Bornology BigOperators Uniformity Topology NNReal ENNReal

noncomputable section

/-- A copy of a Prod type, on which we will put the `L^p` distance. Since the Prod type itself is
already endowed with the `L^∞` distance, we need the type synonym to avoid confusing typeclass
resolution. Also, we let it depend on `p`, to get a whole family of type on which we can put
different distances. -/
@[nolint unusedArguments]
def ProdLp (_p : ℝ≥0∞) (α β : Type _) : Type _ :=
  α × β

instance (p : ℝ≥0∞) (α β : Type _) [Inhabited α] [Inhabited β] : Inhabited (ProdLp p α β) :=
  ⟨default, default⟩

@[ext]
protected theorem ProdLp.ext {p : ℝ≥0∞} {α β : Type _} {x y : ProdLp p α β}
    (h1 : x.fst = y.fst) (h2 : x.snd = y.snd) : x = y := Prod.ext h1 h2

namespace ProdLp

variable (p : ℝ≥0∞) (𝕜 𝕜' : Type _) (α β : Type _)

/-- Canonical bijection between `PiLp p α` and the original Pi type. We introduce it to be able
to compare the `L^p` and `L^∞` distances through it. -/
protected def equiv : ProdLp p α β ≃ α × β :=
  Equiv.refl _

/-! Note that the unapplied versions of these lemmas are deliberately omitted, as they break
the use of the type synonym. -/

@[simp]
theorem equiv_apply (x : ProdLp p α β) : ProdLp.equiv p α β x = x :=
  rfl

@[simp]
theorem equiv_symm_apply (x : α × β) : (ProdLp.equiv p α β).symm x = x :=
  rfl

section DistNorm

/-!
### Definition of `edist`, `dist` and `norm` on `PiLp`

In this section we define the `edist`, `dist` and `norm` functions on `PiLp p α` without assuming
`[Fact (1 ≤ p)]` or metric properties of the spaces `α i`. This allows us to provide the rewrite
lemmas for each of three cases `p = 0`, `p = ∞` and `0 < p.to_real`.
-/


section Edist

variable [EDist α] [EDist β]

/-- Endowing the space `ProdLp p α β` with the `L^p` edistance. We register this instance
separate from `ProdLp.instPseudoEMetric` since the latter requires the type class hypothesis
`[Fact (1 ≤ p)]` in order to prove the triangle inequality.

Registering this separately allows for a future emetric-like structure on `ProdLp p α β` for `p < 1`
satisfying a relaxed triangle inequality. The terminology for this varies throughout the
literature, but it is sometimes called a *quasi-metric* or *semi-metric*. -/
instance : EDist (ProdLp p α β) where
  edist f g :=
    -- Porting note: can we drop the `_hp` entirely?
    if _hp : p = 0 then 0
    else
      if p = ∞ then edist f.fst g.fst ⊔ edist f.snd g.snd
      else (edist f.fst g.fst ^ p.toReal + edist f.snd g.snd ^ p.toReal) ^ (1 / p.toReal)

variable {α β}

variable (x y : ProdLp p α β) (x' : α × β)

theorem edist_eq_card (f g : ProdLp 0 α β) : edist f g = 0 :=
  if_pos rfl

theorem edist_eq_add {p : ℝ≥0∞} (hp : 0 < p.toReal) (f g : ProdLp p α β) :
    edist f g = (edist f.fst g.fst ^ p.toReal + edist f.snd g.snd ^ p.toReal) ^ (1 / p.toReal) :=
  let hp' := ENNReal.toReal_pos_iff.mp hp
  (if_neg hp'.1.ne').trans (if_neg hp'.2.ne)

theorem edist_eq_sup (f g : ProdLp ∞ α β) :
    edist f g = edist f.fst g.fst ⊔ edist f.snd g.snd := by
  dsimp [edist]
  exact if_neg ENNReal.top_ne_zero

end Edist

section EdistProp

variable {α β}
variable [PseudoEMetricSpace α] [PseudoEMetricSpace β]

/-- This holds independent of `p` and does not require `[Fact (1 ≤ p)]`. We keep it separate
from `pi_Lp.pseudo_emetric_space` so it can be used also for `p < 1`. -/
protected theorem edist_self (f : ProdLp p α β) : edist f f = 0 := by
  rcases p.trichotomy with (rfl | rfl | h)
  · simp [edist_eq_card]
  · simp [edist_eq_sup]
  · simp [edist_eq_add h, ENNReal.zero_rpow_of_pos h, ENNReal.zero_rpow_of_pos (inv_pos.2 <| h)]

/-- This holds independent of `p` and does not require `[Fact (1 ≤ p)]`. We keep it separate
from `pi_Lp.pseudo_emetric_space` so it can be used also for `p < 1`. -/
protected theorem edist_comm (f g : ProdLp p α β) : edist f g = edist g f := by
  rcases p.trichotomy with (rfl | rfl | h)
  · simp only [edist_eq_card, eq_comm, Ne.def]
  · simp only [edist_eq_sup, edist_comm]
  · simp only [edist_eq_add h, edist_comm]

end EdistProp

section Dist

variable [Dist α] [Dist β]

/-- Endowing the space `PiLp p β` with the `L^p` distance. We register this instance
separate from `pi_Lp.pseudo_metric` since the latter requires the type class hypothesis
`[Fact (1 ≤ p)]` in order to prove the triangle inequality.

Registering this separately allows for a future metric-like structure on `PiLp p β` for `p < 1`
satisfying a relaxed triangle inequality. The terminology for this varies throughout the
literature, but it is sometimes called a *quasi-metric* or *semi-metric*. -/
instance : Dist (ProdLp p α β) where
  dist f g :=
    if _hp : p = 0 then 0 --{ i | f i ≠ g i }.toFinite.toFinset.card
    else
      if p = ∞ then dist f.fst g.fst ⊔ dist f.snd g.snd
      else (dist f.fst g.fst ^ p.toReal + dist f.snd g.snd ^ p.toReal) ^ (1 / p.toReal)

variable {α β}

theorem dist_eq_card (f g : ProdLp 0 α β) : dist f g = 0 :=
  if_pos rfl

theorem dist_eq_add {p : ℝ≥0∞} (hp : 0 < p.toReal) (f g : ProdLp p α β) :
    dist f g = (dist f.fst g.fst ^ p.toReal + dist f.snd g.snd ^ p.toReal) ^ (1 / p.toReal) :=
  let hp' := ENNReal.toReal_pos_iff.mp hp
  (if_neg hp'.1.ne').trans (if_neg hp'.2.ne)

theorem dist_eq_sup (f g : ProdLp ∞ α β) :
    dist f g = dist f.fst g.fst ⊔ dist f.snd g.snd := by
  dsimp [dist]
  exact if_neg ENNReal.top_ne_zero

end Dist

section Norm

variable [Norm α] [Zero α] [Norm β] [Zero β]

/-- Endowing the space `PiLp p β` with the `L^p` norm. We register this instance
separate from `PiLp.seminormedAddCommGroup` since the latter requires the type class hypothesis
`[Fact (1 ≤ p)]` in order to prove the triangle inequality.

Registering this separately allows for a future norm-like structure on `PiLp p β` for `p < 1`
satisfying a relaxed triangle inequality. These are called *quasi-norms*. -/
instance instNorm : Norm (ProdLp p α β) where
  norm f :=
    if _hp : p = 0 then 0 -- { i | f i ≠ 0 }.toFinite.toFinset.card
    else if p = ∞ then ‖f.fst‖ ⊔ ‖f.snd‖
    else (‖f.fst‖ ^ p.toReal + ‖f.snd‖ ^ p.toReal) ^ (1 / p.toReal)

variable {p β}

theorem norm_eq_card (f : ProdLp 0 α β) : ‖f‖ = 0 :=
  if_pos rfl

theorem norm_eq_sup (f : ProdLp ∞ α β) : ‖f‖ = ‖f.fst‖ ⊔ ‖f.snd‖ := by
  dsimp [Norm.norm]
  exact if_neg ENNReal.top_ne_zero

theorem norm_eq_add (hp : 0 < p.toReal) (f : ProdLp p α β) :
    ‖f‖ = (‖f.fst‖ ^ p.toReal + ‖f.snd‖ ^ p.toReal) ^ (1 / p.toReal) :=
  let hp' := ENNReal.toReal_pos_iff.mp hp
  (if_neg hp'.1.ne').trans (if_neg hp'.2.ne)

end Norm

end DistNorm

section Aux

/-!
### The uniformity on finite `L^p` products is the product uniformity

In this section, we put the `L^p` edistance on `PiLp p α`, and we check that the uniformity
coming from this edistance coincides with the product uniformity, by showing that the canonical
map to the Pi type (with the `L^∞` distance) is a uniform embedding, as it is both Lipschitz and
antiLipschitz.

We only register this emetric space structure as a temporary instance, as the true instance (to be
registered later) will have as uniformity exactly the product uniformity, instead of the one coming
from the edistance (which is equal to it, but not defeq). See Note [forgetful inheritance]
explaining why having definitionally the right uniformity is often important.
-/


variable [Fact (1 ≤ p)] --[∀ i, PseudoMetricSpace (α i)] [∀ i, PseudoEMetricSpace (β i)]

/-- Endowing the space `PiLp p β` with the `L^p` pseudoemetric structure. This definition is not
satisfactory, as it does not register the fact that the topology and the uniform structure coincide
with the product one. Therefore, we do not register it as an instance. Using this as a temporary
pseudoemetric space instance, we will show that the uniform structure is equal (but not defeq) to
the product one, and then register an instance in which we replace the uniform structure by the
product one using this pseudoemetric space and `PseudoEMetricSpace.replaceUniformity`. -/
def pseudoEmetricAux [PseudoEMetricSpace α] [PseudoEMetricSpace β] :
    PseudoEMetricSpace (ProdLp p α β) where
  edist_self := ProdLp.edist_self p
  edist_comm := ProdLp.edist_comm p
  edist_triangle f g h := by
    rcases p.dichotomy with (rfl | hp)
    · simp only [edist_eq_sup]
      exact sup_le ((edist_triangle _ g.fst _).trans <| add_le_add le_sup_left le_sup_left)
        ((edist_triangle _ g.snd _).trans <| add_le_add le_sup_right le_sup_right)
    · simp only [edist_eq_add (zero_lt_one.trans_le hp)]
      calc
        (edist f.fst h.fst ^ p.toReal + edist f.snd h.snd ^ p.toReal) ^ (1 / p.toReal) ≤
            ((edist f.fst g.fst + edist g.fst h.fst) ^ p.toReal +
              (edist f.snd g.snd + edist g.snd h.snd) ^ p.toReal) ^ (1 / p.toReal) := by
          apply ENNReal.rpow_le_rpow _ (one_div_nonneg.2 <| zero_le_one.trans hp)
          exact add_le_add (ENNReal.rpow_le_rpow (edist_triangle _ _ _) (zero_le_one.trans hp))
            (ENNReal.rpow_le_rpow (edist_triangle _ _ _) (zero_le_one.trans hp))
        _ ≤
            (edist f.fst g.fst ^ p.toReal + edist f.snd g.snd ^ p.toReal) ^ (1 / p.toReal) +
              (edist g.fst h.fst ^ p.toReal + edist g.snd h.snd ^ p.toReal) ^ (1 / p.toReal) := by
          have := ENNReal.Lp_add_le {0, 1}
            (if · = 0 then edist f.fst g.fst else edist f.snd g.snd)
            (if · = 0 then edist g.fst h.fst else edist g.snd h.snd) hp
          simp only [Finset.mem_singleton, not_false_eq_true, Finset.sum_insert,
            Finset.sum_singleton] at this
          exact this

attribute [local instance] ProdLp.pseudoEmetricAux

/-- An auxiliary lemma used twice in the proof of `PiLp.pseudoMetricAux` below. Not intended for
use outside this file. -/
theorem sup_edist_ne_top_aux {α β : Type _}
    [PseudoMetricSpace α] [PseudoMetricSpace β] (f g : ProdLp ∞ α β) :
    edist f.fst g.fst ⊔ edist f.snd g.snd ≠ ⊤ := by
  refine ne_of_lt ?_
  simp [edist, PseudoMetricSpace.edist_dist]

/-- Endowing the space `PiLp p α` with the `L^p` pseudometric structure. This definition is not
satisfactory, as it does not register the fact that the topology, the uniform structure, and the
bornology coincide with the product ones. Therefore, we do not register it as an instance. Using
this as a temporary pseudoemetric space instance, we will show that the uniform structure is equal
(but not defeq) to the product one, and then register an instance in which we replace the uniform
structure and the bornology by the product ones using this pseudometric space,
`PseudoMetricSpace.replaceUniformity`, and `PseudoMetricSpace.replaceBornology`.

See note [reducible non-instances] -/
@[reducible]
def pseudoMetricAux [PseudoMetricSpace α] [PseudoMetricSpace β] :
    PseudoMetricSpace (ProdLp p α β) :=
  PseudoEMetricSpace.toPseudoMetricSpaceOfDist dist
    (fun f g => by
      rcases p.dichotomy with (rfl | h)
      · exact sup_edist_ne_top_aux f g
      · rw [edist_eq_add (zero_lt_one.trans_le h)]
        refine
          ENNReal.rpow_ne_top_of_nonneg (one_div_nonneg.2 (zero_le_one.trans h)) (ne_of_lt ?_)
        simp [ENNReal.add_lt_top, ENNReal.rpow_lt_top_of_nonneg, edist_ne_top] )
    fun f g => by
    rcases p.dichotomy with (rfl | h)
    · rw [edist_eq_sup, dist_eq_sup]
      refine' le_antisymm (sup_le _ _) _
      · rw [← ENNReal.ofReal_le_iff_le_toReal (sup_edist_ne_top_aux f g), ←
          PseudoMetricSpace.edist_dist]
        exact le_sup_left
      · rw [← ENNReal.ofReal_le_iff_le_toReal (sup_edist_ne_top_aux f g), ←
          PseudoMetricSpace.edist_dist]
        exact le_sup_right
      · refine ENNReal.toReal_le_of_le_ofReal ?_ ?_
        · simp only [ge_iff_le, le_sup_iff, dist_nonneg]
        · change PseudoMetricSpace.edist _ _ ⊔ PseudoMetricSpace.edist _ _ ≤ _
          simp [PseudoMetricSpace.edist_dist, ENNReal.ofReal_le_ofReal]
    · have h1 : edist f.fst g.fst ^ p.toReal ≠ ⊤ :=
        ENNReal.rpow_ne_top_of_nonneg (zero_le_one.trans h) (edist_ne_top _ _)
      have h2 : edist f.snd g.snd ^ p.toReal ≠ ⊤ :=
        ENNReal.rpow_ne_top_of_nonneg (zero_le_one.trans h) (edist_ne_top _ _)
      simp only [edist_eq_add (zero_lt_one.trans_le h), dist_edist, ENNReal.toReal_rpow,
        dist_eq_add (zero_lt_one.trans_le h), ← ENNReal.toReal_add h1 h2]

attribute [local instance] ProdLp.pseudoMetricAux

theorem lipschitzWith_equiv_aux : LipschitzWith 1 (PiLp.equiv p β) := by
  intro x y
  rcases p.dichotomy with (rfl | h)
  · simpa only [ENNReal.coe_one, one_mul, edist_eq_iSup, edist, Finset.sup_le_iff, Finset.mem_univ,
      forall_true_left] using le_iSup fun i => edist (x i) (y i)
  · have cancel : p.toReal * (1 / p.toReal) = 1 := mul_div_cancel' 1 (zero_lt_one.trans_le h).ne'
    rw [edist_eq_sum (zero_lt_one.trans_le h)]
    simp only [edist, forall_prop_of_true, one_mul, Finset.mem_univ, Finset.sup_le_iff,
      ENNReal.coe_one]
    intro i
    calc
      edist (x i) (y i) = (edist (x i) (y i) ^ p.toReal) ^ (1 / p.toReal) := by
        simp [← ENNReal.rpow_mul, cancel, -one_div]
      _ ≤ (∑ i, edist (x i) (y i) ^ p.toReal) ^ (1 / p.toReal) := by
        apply ENNReal.rpow_le_rpow _ (one_div_nonneg.2 <| zero_le_one.trans h)
        exact Finset.single_le_sum (fun i _ => (bot_le : (0 : ℝ≥0∞) ≤ _)) (Finset.mem_univ i)
#align pi_Lp.lipschitz_with_equiv_aux PiLp.lipschitzWith_equiv_aux

theorem antilipschitzWith_equiv_aux :
    AntilipschitzWith ((Fintype.card ι : ℝ≥0) ^ (1 / p).toReal) (PiLp.equiv p β) := by
  intro x y
  rcases p.dichotomy with (rfl | h)
  · simp only [edist_eq_iSup, ENNReal.div_top, ENNReal.zero_toReal, NNReal.rpow_zero,
      ENNReal.coe_one, one_mul, iSup_le_iff]
    -- Porting note: `Finset.le_sup` needed some help
    exact fun i => Finset.le_sup (f := fun i => edist (x i) (y i)) (Finset.mem_univ i)
  · have pos : 0 < p.toReal := zero_lt_one.trans_le h
    have nonneg : 0 ≤ 1 / p.toReal := one_div_nonneg.2 (le_of_lt pos)
    have cancel : p.toReal * (1 / p.toReal) = 1 := mul_div_cancel' 1 (ne_of_gt pos)
    rw [edist_eq_sum pos, ENNReal.toReal_div 1 p]
    simp only [edist, ← one_div, ENNReal.one_toReal]
    calc
      (∑ i, edist (x i) (y i) ^ p.toReal) ^ (1 / p.toReal) ≤
          (∑ _i, edist (PiLp.equiv p β x) (PiLp.equiv p β y) ^ p.toReal) ^ (1 / p.toReal) := by
        refine ENNReal.rpow_le_rpow ?_ nonneg
        swap
        refine Finset.sum_le_sum fun i _ => ?_
        apply ENNReal.rpow_le_rpow _ (le_of_lt pos)
        exact Finset.le_sup (f := fun i => edist (x i) (y i)) (Finset.mem_univ i)
      _ =
          ((Fintype.card ι : ℝ≥0) ^ (1 / p.toReal) : ℝ≥0) *
            edist (PiLp.equiv p β x) (PiLp.equiv p β y) := by
        simp only [nsmul_eq_mul, Finset.card_univ, ENNReal.rpow_one, Finset.sum_const,
          ENNReal.mul_rpow_of_nonneg _ _ nonneg, ← ENNReal.rpow_mul, cancel]
        have : (Fintype.card ι : ℝ≥0∞) = (Fintype.card ι : ℝ≥0) :=
          (ENNReal.coe_nat (Fintype.card ι)).symm
        rw [this, ENNReal.coe_rpow_of_nonneg _ nonneg]
#align pi_Lp.antilipschitz_with_equiv_aux PiLp.antilipschitzWith_equiv_aux

theorem aux_uniformity_eq : 𝓤 (PiLp p β) = 𝓤[Pi.uniformSpace _] := by
  have A : UniformInducing (PiLp.equiv p β) :=
    (antilipschitzWith_equiv_aux p β).uniformInducing
      (lipschitzWith_equiv_aux p β).uniformContinuous
  have : (fun x : PiLp p β × PiLp p β => ((PiLp.equiv p β) x.fst, (PiLp.equiv p β) x.snd)) = id :=
    by ext i <;> rfl
  rw [← A.comap_uniformity, this, comap_id]
#align pi_Lp.aux_uniformity_eq PiLp.aux_uniformity_eq

theorem aux_cobounded_eq : cobounded (PiLp p α) = @cobounded _ Pi.instBornology :=
  calc
    cobounded (PiLp p α) = comap (PiLp.equiv p α) (cobounded _) :=
      le_antisymm (antilipschitzWith_equiv_aux p α).tendsto_cobounded.le_comap
        (lipschitzWith_equiv_aux p α).comap_cobounded_le
    _ = _ := comap_id
#align pi_Lp.aux_cobounded_eq PiLp.aux_cobounded_eq

end Aux

/-! ### Instances on finite `L^p` products -/


instance instUniformSpace [UniformSpace α] [UniformSpace β] : UniformSpace (ProdLp p α β) :=
  instUniformSpaceProd

theorem uniformContinuous_equiv [UniformSpace α] [UniformSpace β] :
    UniformContinuous (ProdLp.equiv p α β) :=
  uniformContinuous_id

theorem uniformContinuous_equiv_symm [UniformSpace α] [UniformSpace β] :
    UniformContinuous (ProdLp.equiv p α β).symm :=
  uniformContinuous_id

@[continuity]
theorem continuous_equiv [UniformSpace α] [UniformSpace β] : Continuous (ProdLp.equiv p α β) :=
  continuous_id

@[continuity]
theorem continuous_equiv_symm [UniformSpace α] [UniformSpace β] :
    Continuous (ProdLp.equiv p α β).symm :=
  continuous_id

instance instBornology [Bornology α] [Bornology β] : Bornology (ProdLp p α β) :=
  Prod.instBornology

-- throughout the rest of the file, we assume `1 ≤ p`
variable [Fact (1 ≤ p)]

/-- pseudoemetric space instance on the product of finitely many pseudoemetric spaces, using the
`L^p` pseudoedistance, and having as uniformity the product uniformity. -/
instance [PseudoEMetricSpace α] [PseudoEMetricSpace β] : PseudoEMetricSpace (ProdLp p α β) :=
  (pseudoEmetricAux p α β).replaceUniformity (aux_uniformity_eq p β).symm

/-- emetric space instance on the product of finitely many emetric spaces, using the `L^p`
edistance, and having as uniformity the product uniformity. -/
instance [EMetricSpace α] [EMetricSpace β] : EMetricSpace (ProdLp p α β) :=
  @EMetricSpace.ofT0PseudoEMetricSpace (ProdLp p α β) _ Prod.instT0Space

/-- pseudometric space instance on the product of finitely many pseudometric spaces, using the
`L^p` distance, and having as uniformity the product uniformity. -/
instance [∀ i, PseudoMetricSpace (β i)] : PseudoMetricSpace (PiLp p β) :=
  ((pseudoMetricAux p β).replaceUniformity (aux_uniformity_eq p β).symm).replaceBornology fun s =>
    Filter.ext_iff.1 (aux_cobounded_eq p β).symm sᶜ

/-- metric space instance on the product of finitely many metric spaces, using the `L^p` distance,
and having as uniformity the product uniformity. -/
instance [∀ i, MetricSpace (α i)] : MetricSpace (PiLp p α) :=
  MetricSpace.ofT0PseudoMetricSpace _
