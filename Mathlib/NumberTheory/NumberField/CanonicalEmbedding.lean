/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.Algebra.Module.Zlattice
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.NumberTheory.NumberField.Embeddings
import Mathlib.RingTheory.Discriminant

import Mathlib.Sandbox

#align_import number_theory.number_field.canonical_embedding from "leanprover-community/mathlib"@"60da01b41bbe4206f05d34fd70c8dd7498717a30"

/-!
# Canonical embedding of a number field

The canonical embedding of a number field `K` of degree `n` is the ring homomorphism
`K →+* ℂ^n` that sends `x ∈ K` to `(φ_₁(x),...,φ_n(x))` where the `φ_i`'s are the complex
embeddings of `K`. Note that we do not choose an ordering of the embeddings, but instead map `K`
into the type `(K →+* ℂ) → ℂ` of `ℂ`-vectors indexed by the complex embeddings.

## Main definitions and results

* `canonicalEmbedding`: the ring homorphism `K →+* ((K →+* ℂ) → ℂ)` defined by sending `x : K` to
the vector `(φ x)` indexed by `φ : K →+* ℂ`.

* `canonicalEmbedding.integerLattice.inter_ball_finite`: the intersection of the
image of the ring of integers by the canonical embedding and any ball centered at `0` of finite
radius is finite.

* `mixedEmbedding`: the ring homomorphism from `K →+* ({ w // IsReal w } → ℝ) ×
({ w // IsComplex w } → ℂ)` that sends `x ∈ K` to `(φ_w x)_w` where `φ_w` is the embedding
associated to the infinite place `w`. In particular, if `w` is real then `φ_w : K →+* ℝ` and, if
`w` is complex, `φ_w` is an arbitrary choice between the two complex emebeddings defining the place
`w`.

* `exists_ne_zero_mem_ringOfIntegers_lt`: let `f : InfinitePlace K → ℝ≥0`, if the product
`∏ w, f w` is large enough, proves that there exists a nonzero algebraic integer `a` such
that `w a < f w` for all infinite places `w`.

## Tags

number field, infinite places
-/

variable (K : Type*) [Field K]

namespace NumberField.canonicalEmbedding

open NumberField

/-- The canonical embedding of a number field `K` of degree `n` into `ℂ^n`. -/
def _root_.NumberField.canonicalEmbedding : K →+* ((K →+* ℂ) → ℂ) := Pi.ringHom fun φ => φ

theorem _root_.NumberField.canonicalEmbedding_injective [NumberField K] :
    Function.Injective (NumberField.canonicalEmbedding K) := RingHom.injective _

variable {K}

@[simp]
theorem apply_at (φ : K →+* ℂ) (x : K) : (NumberField.canonicalEmbedding K x) φ = φ x := rfl

open scoped ComplexConjugate

/-- The image of `canonicalEmbedding` lives in the `ℝ`-submodule of the `x ∈ ((K →+* ℂ) → ℂ)` such
that `conj x_φ = x_(conj φ)` for all `∀ φ : K →+* ℂ`. -/
theorem conj_apply {x : ((K →+* ℂ) → ℂ)} (φ : K →+* ℂ)
    (hx : x ∈ Submodule.span ℝ (Set.range (canonicalEmbedding K))) :
    conj (x φ) = x (ComplexEmbedding.conjugate φ) := by
  refine Submodule.span_induction hx ?_ ?_ (fun _ _ hx hy => ?_) (fun a _ hx => ?_)
  · rintro _ ⟨x, rfl⟩
    rw [apply_at, apply_at, ComplexEmbedding.conjugate_coe_eq]
  · rw [Pi.zero_apply, Pi.zero_apply, map_zero]
  · rw [Pi.add_apply, Pi.add_apply, map_add, hx, hy]
  · rw [Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]
    exact congrArg ((a : ℂ) * ·) hx

theorem nnnorm_eq [NumberField K] (x : K) :
    ‖canonicalEmbedding K x‖₊ = Finset.univ.sup (fun φ : K →+* ℂ => ‖φ x‖₊) := by
  simp_rw [Pi.nnnorm_def, apply_at]

theorem norm_le_iff [NumberField K] (x : K) (r : ℝ) :
    ‖canonicalEmbedding K x‖ ≤ r ↔ ∀ φ : K →+* ℂ, ‖φ x‖ ≤ r := by
  obtain hr | hr := lt_or_le r 0
  · obtain ⟨φ⟩ := (inferInstance : Nonempty (K →+* ℂ))
    refine iff_of_false ?_ ?_
    exact (hr.trans_le (norm_nonneg _)).not_le
    exact fun h => hr.not_le (le_trans (norm_nonneg _) (h φ))
  · lift r to NNReal using hr
    simp_rw [← coe_nnnorm, nnnorm_eq, NNReal.coe_le_coe, Finset.sup_le_iff, Finset.mem_univ,
      forall_true_left]

variable (K)

/-- The image of `𝓞 K` as a subring of `ℂ^n`. -/
def integerLattice : Subring ((K →+* ℂ) → ℂ) :=
  (RingHom.range (algebraMap (𝓞 K) K)).map (canonicalEmbedding K)

theorem integerLattice.inter_ball_finite [NumberField K] (r : ℝ) :
    ((integerLattice K : Set ((K →+* ℂ) → ℂ)) ∩ Metric.closedBall 0 r).Finite := by
  obtain hr | _ := lt_or_le r 0
  · simp [Metric.closedBall_eq_empty.2 hr]
  · have heq : ∀ x, canonicalEmbedding K x ∈ Metric.closedBall 0 r ↔
        ∀ φ : K →+* ℂ, ‖φ x‖ ≤ r := by
      intro x; rw [← norm_le_iff, mem_closedBall_zero_iff]
    convert (Embeddings.finite_of_norm_le K ℂ r).image (canonicalEmbedding K)
    ext; constructor
    · rintro ⟨⟨_, ⟨x, rfl⟩, rfl⟩, hx⟩
      exact ⟨↑x, ⟨SetLike.coe_mem x, fun φ => (heq x).mp hx φ⟩, rfl⟩
    · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
      exact ⟨⟨x, ⟨⟨x, hx1⟩, rfl⟩, rfl⟩, (heq x).mpr hx2⟩

open Module Fintype FiniteDimensional

/-- A `ℂ`-basis of `ℂ^n` that is also a `ℤ`-basis of the `integerLattice`. -/
noncomputable def latticeBasis [NumberField K] :
    Basis (Free.ChooseBasisIndex ℤ (𝓞 K)) ℂ ((K →+* ℂ) → ℂ) := by
  classical
  -- Let `B` be the canonical basis of `(K →+* ℂ) → ℂ`. We prove that the determinant of
  -- the image by `canonicalEmbedding` of the integral basis of `K` is nonzero. This
  -- will imply the result.
    let B := Pi.basisFun ℂ (K →+* ℂ)
    let e : (K →+* ℂ) ≃ Free.ChooseBasisIndex ℤ (𝓞 K) :=
      equivOfCardEq ((Embeddings.card K ℂ).trans (finrank_eq_card_basis (integralBasis K)))
    let M := B.toMatrix (fun i => canonicalEmbedding K (integralBasis K (e i)))
    suffices M.det ≠ 0 by
      rw [← isUnit_iff_ne_zero, ← Basis.det_apply, ← is_basis_iff_det] at this
      refine basisOfLinearIndependentOfCardEqFinrank
        ((linearIndependent_equiv e.symm).mpr this.1) ?_
      rw [← finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank, finrank_fintype_fun_eq_card,
        Embeddings.card]
  -- In order to prove that the determinant is nonzero, we show that it is equal to the
  -- square of the discriminant of the integral basis and thus it is not zero
    let N := Algebra.embeddingsMatrixReindex ℚ ℂ (fun i => integralBasis K (e i))
      RingHom.equivRatAlgHom
    rw [show M = N.transpose by { ext:2; rfl }]
    rw [Matrix.det_transpose, ← @pow_ne_zero_iff ℂ _ _ _ 2 (by norm_num)]
    convert (map_ne_zero_iff _ (algebraMap ℚ ℂ).injective).mpr
      (Algebra.discr_not_zero_of_basis ℚ (integralBasis K))
    rw [← Algebra.discr_reindex ℚ (integralBasis K) e.symm]
    exact (Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ
      (fun i => integralBasis K (e i)) RingHom.equivRatAlgHom).symm

@[simp]
theorem latticeBasis_apply [NumberField K] (i : Free.ChooseBasisIndex ℤ (𝓞 K)) :
    latticeBasis K i = (canonicalEmbedding K) (integralBasis K i) := by
  simp only [latticeBasis, integralBasis_apply, coe_basisOfLinearIndependentOfCardEqFinrank,
    Function.comp_apply, Equiv.apply_symm_apply]

theorem mem_span_latticeBasis [NumberField K] (x : (K →+* ℂ) → ℂ) :
    x ∈ Submodule.span ℤ (Set.range (latticeBasis K)) ↔ x ∈ canonicalEmbedding K '' (𝓞 K) := by
  rw [show Set.range (latticeBasis K) =
      (canonicalEmbedding K).toIntAlgHom.toLinearMap '' (Set.range (integralBasis K)) by
    rw [← Set.range_comp]; exact congrArg Set.range (funext (fun i => latticeBasis_apply K i))]
  rw [← Submodule.map_span, ← SetLike.mem_coe, Submodule.map_coe]
  rw [show (Submodule.span ℤ (Set.range (integralBasis K)) : Set K) = 𝓞 K by
    ext; exact mem_span_integralBasis K]
  rfl

end NumberField.canonicalEmbedding

namespace NumberField.mixedEmbedding

open NumberField NumberField.InfinitePlace  FiniteDimensional

/-- The ambient space `ℝ^r₁ × ℂ^r₂` with `(r₁, r₂)` the signature of `K`. -/
local notation "E" K =>
  ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℂ)

/-- The mixed embedding of a number field `K` of signature `(r₁, r₂)` into `ℝ^r₁ × ℂ^r₂`. -/
noncomputable def _root_.NumberField.mixedEmbedding : K →+* (E K) :=
  RingHom.prod (Pi.ringHom fun w => embedding_of_isReal w.prop)
    (Pi.ringHom fun w => w.val.embedding)

instance [NumberField K] :  Nontrivial (E K) := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  obtain hw | hw := w.isReal_or_isComplex
  · have : Nonempty {w : InfinitePlace K // IsReal w} := ⟨⟨w, hw⟩⟩
    exact nontrivial_prod_left
  · have : Nonempty {w : InfinitePlace K // IsComplex w} := ⟨⟨w, hw⟩⟩
    exact nontrivial_prod_right

theorem rank_space [NumberField K] : finrank ℝ (E K) = finrank ℚ K := by
  classical
  rw [finrank_prod, finrank_pi, finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const,
    Finset.card_univ, ← card_real_embeddings, Algebra.id.smul_eq_mul, mul_comm,
    ← card_complex_embeddings, ← NumberField.Embeddings.card K ℂ, Fintype.card_subtype_compl,
    Nat.add_sub_of_le (Fintype.card_subtype_le _)]

theorem _root_.NumberField.mixedEmbedding_injective [NumberField K] :
    Function.Injective (NumberField.mixedEmbedding K) := by
  exact RingHom.injective _

section comm_map

open InfinitePlace
/-- The linear map that makes `canonicalEmbedding` and `mixedEmbedding` commute, see
`comm_map_canonical_eq_mixed`. -/
noncomputable def comm_map : ((K →+* ℂ) → ℂ) →ₗ[ℝ] (E K) :=
{ toFun := fun x => ⟨fun w => (x w.val.embedding).re, fun w => x w.val.embedding⟩
  map_add' := by
    simp only [Pi.add_apply, Complex.add_re, Prod.mk_add_mk, Prod.mk.injEq]
    exact fun _ _ => ⟨rfl, rfl⟩
  map_smul' := by
    simp only [Pi.smul_apply, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, RingHom.id_apply, Prod.smul_mk, Prod.mk.injEq]
    exact fun _ _ => ⟨rfl, rfl⟩ }

theorem comm_map_apply_of_isReal (x : (K →+* ℂ) → ℂ) {w : InfinitePlace K} (hw : IsReal w) :
  (comm_map K x).1 ⟨w, hw⟩ = (x w.embedding).re := rfl

theorem comm_map_apply_of_isComplex (x : (K →+* ℂ) → ℂ) {w : InfinitePlace K} (hw : IsComplex w) :
  (comm_map K x).2 ⟨w, hw⟩ = x w.embedding := rfl

@[simp]
theorem comm_map_canonical_eq_mixed (x : K) :
    comm_map K (canonicalEmbedding K x) = mixedEmbedding K x := by
  simp only [canonicalEmbedding, comm_map, LinearMap.coe_mk, AddHom.coe_mk, Pi.ringHom_apply,
    mixedEmbedding, RingHom.prod_apply, Prod.mk.injEq]
  exact ⟨rfl, rfl⟩

/-- This is a technical result to ensure that the image of the `ℂ`-basis of `ℂ^n` defined in
`canonicalEmbedding.latticeBasis` is a `ℝ`-basis of `ℝ^r₁ × ℂ^r₂`,
see `mixedEmbedding.latticeBasis`. -/
theorem disjoint_span_comm_map_ker [NumberField K]:
    Disjoint (Submodule.span ℝ (Set.range (canonicalEmbedding.latticeBasis K)))
      (LinearMap.ker (comm_map K)) := by
  refine LinearMap.disjoint_ker.mpr (fun x h_mem h_zero => ?_)
  replace h_mem : x ∈ Submodule.span ℝ (Set.range (canonicalEmbedding K)) := by
    refine (Submodule.span_mono ?_) h_mem
    rintro _ ⟨i, rfl⟩
    exact ⟨integralBasis K i, (canonicalEmbedding.latticeBasis_apply K i).symm⟩
  ext1 φ
  rw [Pi.zero_apply]
  by_cases hφ : ComplexEmbedding.IsReal φ
  · rw [show x φ = (x φ).re by
      rw [eq_comm, ← Complex.conj_eq_iff_re, canonicalEmbedding.conj_apply _ h_mem,
        ComplexEmbedding.isReal_iff.mp hφ], ← Complex.ofReal_zero]
    congr
    rw [← embedding_mk_eq_of_isReal hφ, ← comm_map_apply_of_isReal K x ⟨φ, hφ, rfl⟩]
    exact congrFun (congrArg (fun x => x.1) h_zero) ⟨InfinitePlace.mk φ, _⟩
  · have := congrFun (congrArg (fun x => x.2) h_zero) ⟨InfinitePlace.mk φ, ⟨φ, hφ, rfl⟩⟩
    cases embedding_mk_eq φ with
    | inl h => rwa [← h, ← comm_map_apply_of_isComplex K x ⟨φ, hφ, rfl⟩]
    | inr h =>
        apply RingHom.injective (starRingEnd ℂ)
        rwa [canonicalEmbedding.conj_apply _ h_mem, ← h, map_zero,
          ← comm_map_apply_of_isComplex K x ⟨φ, hφ, rfl⟩]

end comm_map

noncomputable section stdBasis

variable [NumberField K]

open Classical Complex MeasureTheory MeasureTheory.Measure Zspan Matrix BigOperators
  ComplexConjugate

variable [NumberField K]

/-- The type indexing the basis `stdBasis`. -/
abbrev index := {w : InfinitePlace K // IsReal w} ⊕ ({w : InfinitePlace K // IsComplex w}) × (Fin 2)

/-- The `ℝ`-basis of `({w // IsReal w} → ℝ) × ({ w // IsComplex w } → ℂ)` formed of the vector
equal to `1` at `w` and `0` elsewhere for `IsReal w` and of the couple of vectors equal to `1`
(resp. `I`) at `w` and `0` elsewhere for `IsComplex w`. -/
def stdBasis : Basis (index K) ℝ (E K) :=
  Basis.prod (Pi.basisFun ℝ _)
    (Basis.reindex (Pi.basis fun _ => basisOneI) (Equiv.sigmaEquivProd _ _))

variable {K}

@[simp]
theorem stdBasis_apply_ofIsReal (x : E K) (w : {w : InfinitePlace K // IsReal w}) :
    (stdBasis K).repr x (Sum.inl w) = x.1 w := rfl

@[simp]
theorem stdBasis_apply_ofIsComplex_fst (x : E K) (w : {w : InfinitePlace K // IsComplex w}) :
    (stdBasis K).repr x (Sum.inr ⟨w, 0⟩) = (x.2 w).re := rfl

@[simp]
theorem stdBasis_apply_ofIsComplex_snd (x : E K) (w : {w : InfinitePlace K // IsComplex w}) :
    (stdBasis K).repr x (Sum.inr ⟨w, 1⟩) = (x.2 w).im := rfl

variable (K)

theorem volume_fundamentalDomain_stdBasis :
    volume (fundamentalDomain (stdBasis K)) = 1 := by
  rw [show fundamentalDomain (stdBasis K) =
        (Set.univ.pi fun _ => Set.Ico 0 1) ×ˢ
        (Set.univ.pi fun _ => Complex.measurableEquivPi⁻¹' (Set.univ.pi fun _ => Set.Ico 0 1)) by
      ext x; simp [stdBasis, mem_fundamentalDomain, Complex.measurableEquivPi],
    volume_eq_prod, prod_prod, volume_pi, volume_pi, pi_pi, pi_pi, Real.volume_Ico,
    sub_zero, ENNReal.ofReal_one, Finset.prod_const_one, one_mul,
    Complex.volume_preserving_equiv_pi.measure_preimage ?_, volume_pi, pi_pi, Real.volume_Ico,
    sub_zero, ENNReal.ofReal_one, Finset.prod_const_one, Finset.prod_const_one]
  exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ico)

/-- The `Equiv` between `index K` and `K →+* ℂ` defined by sending a real infinite place `w` to
the unique corresponding complex embedding `w.embedding`, the pair `⟨w, 0⟩` (resp. `⟨w, 1⟩`) for a
complex infinite place `w` to `w.embedding` (resp. `conjugate w.embedding`). -/
def indexEquiv : (index K) ≃ (K →+* ℂ) := by
  refine Equiv.ofBijective (fun c => ?_)
    ((Fintype.bijective_iff_surjective_and_card _).mpr ⟨?_, ?_⟩)
  · cases c with
    | inl w => exact w.val.embedding
    | inr wj => rcases wj with ⟨w, j⟩
                exact if j = 0 then w.val.embedding else ComplexEmbedding.conjugate w.val.embedding
  · intro φ
    by_cases hφ : ComplexEmbedding.IsReal φ
    · exact ⟨Sum.inl (InfinitePlace.mkReal ⟨φ, hφ⟩), by simp [embedding_mk_eq_of_isReal hφ]⟩
    · by_cases hw : (InfinitePlace.mk φ).embedding = φ
      · exact ⟨Sum.inr ⟨InfinitePlace.mkComplex ⟨φ, hφ⟩, 0⟩, by simp [hw]⟩
      · exact ⟨Sum.inr ⟨InfinitePlace.mkComplex ⟨φ, hφ⟩, 1⟩,
          by simp [(embedding_mk_eq φ).resolve_left hw]⟩
  · rw [Embeddings.card, ← rank_space K, ← FiniteDimensional.finrank_eq_card_basis (stdBasis K)]

variable {K}

@[simp]
theorem indexEquiv_apply_ofIsReal (w : {w : InfinitePlace K // IsReal w}) :
    (indexEquiv K) (Sum.inl w) = w.val.embedding := rfl

@[simp]
theorem indexEquiv_apply_ofIsComplex_fst (w : {w : InfinitePlace K // IsComplex w}) :
    (indexEquiv K) (Sum.inr ⟨w, 0⟩) = w.val.embedding := rfl

@[simp]
theorem indexEquiv_apply_ofIsComplex_snd (w : {w : InfinitePlace K // IsComplex w}) :
    (indexEquiv K) (Sum.inr ⟨w, 1⟩) = ComplexEmbedding.conjugate w.val.embedding := rfl

variable (K)

/-- The matrix that gives the representation on `stdBasis` of the image by `comm_map` of an
element `x` of `(K →+* ℂ) → ℂ` fixed by the transformation `x_φ ↦ conj x_(conjugate φ)`,
see `stdBasis_repr_eq_matrix_to_stdBasis_mul`. -/
def matrix_to_stdBasis : Matrix (index K) (index K) ℂ :=
  fromBlocks (diagonal fun _ => 1) 0 0 <| reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _)
    (blockDiagonal (fun _ => (2 : ℂ)⁻¹ • !![1, 1; - I, I]))

-- See: https://github.com/leanprover/lean4/issues/2220
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

theorem det_matrix_to_stdBasis :
    (matrix_to_stdBasis K).det = (2⁻¹ * I) ^ Fintype.card {w : InfinitePlace K // IsComplex w} :=
  calc
  _ = ∏ k : { w : InfinitePlace K // IsComplex w }, det ((2 : ℂ)⁻¹ • !![1, 1; -I, I]) := by
      rw [matrix_to_stdBasis, det_fromBlocks_zero₂₁, det_diagonal, Finset.prod_const_one, one_mul,
          det_reindex_self, det_blockDiagonal]
  _ = ∏ k : { w : InfinitePlace K // IsComplex w }, (2⁻¹ * Complex.I) := by
      refine Finset.prod_congr (Eq.refl _) (fun _ _ => ?_)
      simp_rw [smul_of, smul_cons, smul_eq_mul, mul_one, smul_empty, det_fin_two_of, mul_neg,
        sub_neg_eq_add, ← mul_add, ← two_mul, inv_mul_cancel_left₀ (two_ne_zero (α := ℂ))]
  _ = (2⁻¹ * Complex.I) ^ Fintype.card {w : InfinitePlace K // IsComplex w} := by
      rw [Finset.prod_const, Fintype.card]

theorem stdBasis_repr_eq_matrix_to_stdBasis_mul (x : (K →+* ℂ) → ℂ)
    (hx : ∀ φ, conj (x φ) = x (ComplexEmbedding.conjugate φ)) (c : index K) :
    ((stdBasis K).repr (comm_map K x) c : ℂ) =
      (mulVec (matrix_to_stdBasis K) (x ∘ (indexEquiv K))) c := by
  simp_rw [comm_map, matrix_to_stdBasis, LinearMap.coe_mk, AddHom.coe_mk,
    mulVec, dotProduct, Function.comp_apply, index, Fintype.sum_sum_type,
    diagonal_one, reindex_apply, ← Finset.univ_product_univ, Finset.sum_product,
    indexEquiv_apply_ofIsReal, Fin.sum_univ_two, indexEquiv_apply_ofIsComplex_fst,
    indexEquiv_apply_ofIsComplex_snd, smul_of, smul_cons, smul_eq_mul,
    mul_one, smul_empty, Equiv.prodComm_symm, Equiv.coe_prodComm]
  cases c with
  | inl w =>
      simp_rw [stdBasis_apply_ofIsReal, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
        one_apply, Matrix.zero_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true, add_zero, Finset.sum_const_zero, add_zero,
        ← conj_eq_iff_re, hx (embedding w.val), conjugate_embedding_eq_of_isReal w.prop]
  | inr c =>
    rcases c with ⟨w, j⟩
    fin_cases j
    · simp_rw [Fin.mk_zero, stdBasis_apply_ofIsComplex_fst, fromBlocks_apply₂₁,
        fromBlocks_apply₂₂, Matrix.zero_apply, submatrix_apply,
        blockDiagonal_apply, Prod.swap_prod_mk, ite_mul, zero_mul, Finset.sum_const_zero,
        zero_add, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
        of_apply, cons_val', cons_val_zero, cons_val_one,
        head_cons, ← hx (embedding w), re_eq_add_conj]
      field_simp
    · simp_rw [Fin.mk_one, stdBasis_apply_ofIsComplex_snd, fromBlocks_apply₂₁,
        fromBlocks_apply₂₂, Matrix.zero_apply, submatrix_apply,
        blockDiagonal_apply, Prod.swap_prod_mk, ite_mul, zero_mul, Finset.sum_const_zero,
        zero_add, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
        of_apply, cons_val', cons_val_zero, cons_val_one,
        head_cons, ← hx (embedding w), im_eq_sub_conj]
      ring_nf; field_simp

end stdBasis

section integerLattice

open Module FiniteDimensional

/-- A `ℝ`-basis of `ℝ^r₁ × ℂ^r₂` that is also a `ℤ`-basis of the image of `𝓞 K`. -/
noncomputable def latticeBasis [NumberField K] :
    Basis (Free.ChooseBasisIndex ℤ (𝓞 K)) ℝ (E K) := by
  classical
    -- We construct an `ℝ`-linear independent family from the image of
    -- `canonicalEmbedding.lattice_basis` by `comm_map`
    have := LinearIndependent.map (LinearIndependent.restrict_scalars
      (by { simpa only [Complex.real_smul, mul_one] using Complex.ofReal_injective })
      (canonicalEmbedding.latticeBasis K).linearIndependent)
      (disjoint_span_comm_map_ker K)
    -- and it's a basis since it has the right cardinality
    refine basisOfLinearIndependentOfCardEqFinrank this ?_
    rw [← finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank, finrank_prod, finrank_pi,
      finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ,
      ← card_real_embeddings, Algebra.id.smul_eq_mul, mul_comm, ← card_complex_embeddings,
      ← NumberField.Embeddings.card K ℂ, Fintype.card_subtype_compl,
      Nat.add_sub_of_le (Fintype.card_subtype_le _)]

@[simp]
theorem latticeBasis_apply [NumberField K] (i : Free.ChooseBasisIndex ℤ (𝓞 K)) :
    latticeBasis K i = (mixedEmbedding K) (integralBasis K i) := by
  simp only [latticeBasis, coe_basisOfLinearIndependentOfCardEqFinrank, Function.comp_apply,
    canonicalEmbedding.latticeBasis_apply, integralBasis_apply, comm_map_canonical_eq_mixed]

theorem mem_span_latticeBasis [NumberField K] (x : (E K)) :
    x ∈ Submodule.span ℤ (Set.range (latticeBasis K)) ↔ x ∈ mixedEmbedding K '' (𝓞 K) := by
  rw [show Set.range (latticeBasis K) =
      (mixedEmbedding K).toIntAlgHom.toLinearMap '' (Set.range (integralBasis K)) by
    rw [← Set.range_comp]; exact congrArg Set.range (funext (fun i => latticeBasis_apply K i))]
  rw [← Submodule.map_span, ← SetLike.mem_coe, Submodule.map_coe]
  rw [show (Submodule.span ℤ (Set.range (integralBasis K)) : Set K) = 𝓞 K by
    ext; exact mem_span_integralBasis K]
  rfl

end integerLattice

section minkowski

open ENNReal NNReal MeasureTheory Zspan Classical

variable [NumberField K]

instance : @Measure.IsAddHaarMeasure (E K) _ _ _ volume := Measure.prod.instIsAddHaarMeasure _ _

/-- The bound that appears in Minkowski theorem, see
`MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`. For the
computation of the volume of the fundamental domain of `latticeBasis K`, see
`NumberField.mixedEmbedding.volume_fundamentalDomain_latticeBasis`. -/
noncomputable def minkowski_bound : ℝ≥0∞ :=
  volume (fundamentalDomain (latticeBasis K)) * 2 ^ (finrank ℝ (E K))

theorem minkowski_bound_lt_top : minkowski_bound K < ⊤ := by
  refine mul_lt_top ?_ ?_
  · exact ne_of_lt (fundamentalDomain_bounded (latticeBasis K)).measure_lt_top
  · exact ne_of_lt (pow_lt_top (lt_top_iff_ne_top.mpr two_ne_top) _)

end minkowski

section convex_body_lt

open Metric ENNReal NNReal

variable (f : InfinitePlace K → ℝ≥0)

/-- The convex body defined by `f`: the set of points `x : E` such that `‖x w‖ < f w` for all
infinite places `w`. -/
abbrev convex_body_lt : Set (E K) :=
  (Set.univ.pi (fun w : { w : InfinitePlace K // IsReal w } => ball 0 (f w))) ×ˢ
  (Set.univ.pi (fun w : { w : InfinitePlace K // IsComplex w } => ball 0 (f w)))

theorem convex_body_lt_mem {x : K} :
    mixedEmbedding K x ∈ (convex_body_lt K f) ↔ ∀ w : InfinitePlace K, w x < f w := by
  simp_rw [mixedEmbedding, RingHom.prod_apply, Set.mem_prod, Set.mem_pi, Set.mem_univ,
    forall_true_left, mem_ball_zero_iff, Pi.ringHom_apply, ← Complex.norm_real,
    embedding_of_isReal_apply, Subtype.forall, ← ball_or_left, ← not_isReal_iff_isComplex, em,
    forall_true_left, norm_embedding_eq]

theorem convex_body_lt_symmetric (x : E K) (hx : x ∈ (convex_body_lt K f)) :
    -x ∈ (convex_body_lt K f) := by
  simp only [Set.mem_prod, Prod.fst_neg, Set.mem_pi, Set.mem_univ, Pi.neg_apply,
    mem_ball_zero_iff, norm_neg, Real.norm_eq_abs, forall_true_left, Subtype.forall,
    Prod.snd_neg, Complex.norm_eq_abs, hx] at hx ⊢
  exact hx

theorem convex_body_lt_convex : Convex ℝ (convex_body_lt K f) :=
  Convex.prod (convex_pi (fun _ _ => convex_ball _ _)) (convex_pi (fun _ _ => convex_ball _ _))

open Classical Fintype MeasureTheory MeasureTheory.Measure BigOperators

-- See: https://github.com/leanprover/lean4/issues/2220
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

variable [NumberField K]

/-- The fudge factor that appears in the formula for the volume of `convex_body_lt`. -/
noncomputable abbrev constant_factor : ℝ≥0∞ :=
  (2 : ℝ≥0∞) ^ card {w : InfinitePlace K // IsReal w} *
    (NNReal.pi : ℝ≥0∞) ^ card {w : InfinitePlace K // IsComplex w}

theorem constant_factor_pos : 0 < (constant_factor K) :=
  mul_pos (pow_ne_zero _ (two_ne_zero)) (pow_ne_zero _ (coe_ne_zero.mpr pi_ne_zero))

theorem constant_factor_lt_top : (constant_factor K) < ⊤ := by
  refine mul_lt_top ?_ ?_
  · exact ne_of_lt (pow_lt_top (lt_top_iff_ne_top.mpr two_ne_top) _)
  · exact ne_of_lt (pow_lt_top coe_lt_top _)

/-- The volume of `(convex_body_lt K f)` where `convex_body_lt K f` is the set of points `x`
such that `‖x w‖ < f w` for all infinite places `w`. -/
theorem convex_body_volume :
    volume (convex_body_lt K f) = (constant_factor K) * ∏ w, (f w) ^ (mult w) := by
  refine calc
    _ = (∏ x : {w // InfinitePlace.IsReal w}, ENNReal.ofReal (2 * (f x.val))) *
          ∏ x : {w // InfinitePlace.IsComplex w}, pi * ENNReal.ofReal (f x.val) ^ 2 := by
      simp_rw [volume_eq_prod, prod_prod, volume_pi, pi_pi, Real.volume_ball, Complex.volume_ball]
    _ = (↑2 ^ card {w : InfinitePlace K // InfinitePlace.IsReal w} *
          (∏ x : {w // InfinitePlace.IsReal w}, ENNReal.ofReal (f x.val))) *
          (↑pi ^ card {w : InfinitePlace K // IsComplex w} *
          (∏ x : {w // IsComplex w}, ENNReal.ofReal (f x.val) ^ 2)) := by
      simp_rw [ofReal_mul (by norm_num : 0 ≤ (2 : ℝ)), Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, ofReal_ofNat]
    _ = (constant_factor K) * ((∏ x : {w // InfinitePlace.IsReal w}, ENNReal.ofReal (f x.val)) *
        (∏ x : {w // IsComplex w}, ENNReal.ofReal (f x.val) ^ 2)) := by ring
    _ = (constant_factor K) * ∏ w, (f w) ^ (mult w) := by
      simp_rw [mult, pow_ite, pow_one, Finset.prod_ite, ofReal_coe_nnreal, not_isReal_iff_isComplex,
        coe_mul, coe_finset_prod, ENNReal.coe_pow]
      congr 2
      · refine (Finset.prod_subtype (Finset.univ.filter _) ?_ (fun w => (f w : ℝ≥0∞))).symm
        exact fun _ => by simp only [Finset.mem_univ, forall_true_left, Finset.mem_filter, true_and]
      · refine (Finset.prod_subtype (Finset.univ.filter _) ?_ (fun w => (f w : ℝ≥0∞) ^ 2)).symm
        exact fun _ => by simp only [Finset.mem_univ, forall_true_left, Finset.mem_filter, true_and]

variable {f}

/-- This is a technical result: quite often, we want to impose conditions at all infinite places
but one and choose the value at the remaining place so that we can apply
`exists_ne_zero_mem_ring_of_integers_lt`. -/
theorem adjust_f {w₁ : InfinitePlace K} (B : ℝ≥0) (hf : ∀ w, w ≠ w₁→ f w ≠ 0) :
    ∃ g : InfinitePlace K → ℝ≥0, (∀ w, w ≠ w₁ → g w = f w) ∧ ∏ w, (g w) ^ mult w = B := by
  let S := ∏ w in Finset.univ.erase w₁, (f w) ^ mult w
  refine ⟨Function.update f w₁ ((B * S⁻¹) ^ (mult w₁ : ℝ)⁻¹), ?_, ?_⟩
  · exact fun w hw => Function.update_noteq hw _ f
  · rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w₁), Function.update_same,
      Finset.prod_congr rfl fun w hw => by rw [Function.update_noteq (Finset.ne_of_mem_erase hw)],
      ← NNReal.rpow_nat_cast, ← NNReal.rpow_mul, inv_mul_cancel, NNReal.rpow_one, mul_assoc,
      inv_mul_cancel, mul_one]
    · rw [Finset.prod_ne_zero_iff]
      exact fun w hw => pow_ne_zero _ (hf w (Finset.ne_of_mem_erase hw))
    · rw [mult]; split_ifs <;> norm_num

variable {f : InfinitePlace K → ℝ≥0}

/-- Assume that `f : InfinitePlace K → ℝ≥0` is such that
`minkowski_bound K < volume (convex_body_lt K f)` where `convex_body_lt K f` is the set of
points `x` such that `‖x w‖ < f w` for all infinite places `w` (see `convex_body_lt_volume` for
the computation of this volume), then there exists a nonzero algebraic integer `a` in `𝓞 K` such
that `w a < f w` for all infinite places `w`. -/
theorem exists_ne_zero_mem_ringOfIntegers_lt (h : minkowski_bound K < volume (convex_body_lt K f)) :
    ∃ (a : 𝓞 K), a ≠ 0 ∧ ∀ w : InfinitePlace K, w a < f w := by
  have h_fund := Zspan.isAddFundamentalDomain (latticeBasis K) volume
  have : Countable (Submodule.span ℤ (Set.range (latticeBasis K))).toAddSubgroup := by
    change Countable (Submodule.span ℤ (Set.range (latticeBasis K)): Set (E K))
    infer_instance
  obtain ⟨⟨x, hx⟩, h_nzr, h_mem⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    h_fund h (convex_body_lt_symmetric K f) (convex_body_lt_convex K f)
  rw [Submodule.mem_toAddSubgroup, mem_span_latticeBasis] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  refine ⟨⟨a, ha⟩, ?_, (convex_body_lt_mem K f).mp h_mem⟩
  rw [ne_eq, AddSubgroup.mk_eq_zero_iff, map_eq_zero, ← ne_eq] at h_nzr
  exact Subtype.ne_of_val_ne h_nzr

end convex_body_lt

section convexBodySum

open NNReal BigOperators Classical

variable [NumberField K]  (r c : Type*) [Fintype r] [Fintype c] (B : ℝ)

/-- The convex body equal to the set of points `x : E` such that
`∑ w real, ‖x w‖ + 2 * ∑ w complex, ‖x w‖ ≤ B`. -/
abbrev convexBodySum : Set ((r → ℝ) × (c → ℂ)) := { x | ∑ w, ‖x.1 w‖ + 2 * ∑ w, ‖x.2 w‖ ≤ B }

theorem convexBodySum_mem {x : K} :
    mixedEmbedding K x ∈ (convexBodySum {w // IsReal w} {w //IsComplex w} B) ↔
      ∑ w : {w // InfinitePlace.IsReal w}, w.val x +
        2 * ∑ w : {w // InfinitePlace.IsComplex w}, w.val x ≤ B := by
  simp_rw [Set.mem_setOf_eq, mixedEmbedding, RingHom.prod_apply, Pi.ringHom_apply,
    ← Complex.norm_real, embedding_of_isReal_apply, norm_embedding_eq]

theorem convexBodySum_symmetric (x : (r → ℝ) × (c → ℂ)) (hx : x ∈ (convexBodySum r c B)) :
    -x ∈ (convexBodySum r c B) := by
  simp_rw [Set.mem_setOf_eq, Prod.fst_neg, Prod.snd_neg, Pi.neg_apply, norm_neg]
  exact hx

theorem convexBodySum_convex : Convex ℝ (convexBodySum r c B) := by
  refine Convex_subAdditive ℝ ?_ ?_ B
  · intro x y
    simp_rw [Prod.fst_add, Pi.add_apply, Prod.snd_add]
    refine le_trans (add_le_add
      (Finset.sum_le_sum (fun w _ => norm_add_le (x.1 w) (y.1 w)))
      (mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun w _ => norm_add_le (x.2 w) (y.2 w))) (by norm_num))) ?_
    simp_rw [Finset.sum_add_distrib, mul_add]
    exact le_of_eq (by ring)
  · intro c x hc
    simp_rw [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Complex.real_smul, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg hc, ← Finset.mul_sum]
    exact le_of_eq (by ring)

open MeasureTheory MeasureTheory.Measure ENNReal Real Fintype intervalIntegral

-- See: https://github.com/leanprover/lean4/issues/2220
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

noncomputable abbrev vol : ℝ≥0∞ :=
    ENNReal.ofReal (2 ^ (card r) * (π / 2) ^ (card c) * B ^ (card r + 2 * card c) /
      (card r + 2 * card c).factorial)

theorem convexBodySum_bounded {n : ℕ} :
    Metric.Bounded {x : (Fin n) → ℝ | ∑ i, |x i| ≤ B} := by
  sorry

example {n : ℕ} (B : ℝ) (h : 0 ≤ B) :
    volume {x : (Fin n) → ℝ | ∑ i, |x i| ≤ B} = 2 ^ n * (ENNReal.ofReal B) ^ n / n.factorial := by
  induction n generalizing B with
  | zero =>
      simp [Nat.zero_eq, Finset.univ_eq_empty, Finset.sum_empty, zero_le_coe, Set.setOf_true,
        volume_pi_isEmpty, pow_zero, Nat.cast_one, coe_one, mul_one, Nat.factorial, div_one, h]
  | succ n hn =>
      suffices ∫ a, Set.indicator {x | ∑ i, |x i| ≤ B} (1 : (Fin n.succ → ℝ) → ℝ) a =
          2 ^ n.succ * B ^ n.succ / n.succ.factorial by
        have t1 : volume {x : Fin n.succ → ℝ | ∑ i, |x i| ≤ B} ≠ ⊤ := sorry
        rw [← ENNReal.ofReal_toReal t1]
        rw [← integral_indicator_one, this]
        sorry
        sorry
      calc
        _ = ∫ y, (fun y :  ℝ × (Fin n → ℝ) =>
                (Set.indicator {z : Fin n → ℝ| ∑ i , |z i| ≤ B - |y.1|} 1 y.2 : ℝ)) y := ?_
        _ = ∫ x, (volume {z : Fin n → ℝ | ∑ i, |z i| ≤ B - |x|}).toReal := ?_
        _ = ∫ x, (Set.indicator (Set.Icc (-B) B)
            fun x => (volume {z : Fin n → ℝ | ∑ i, |z i| ≤ B - |x|}).toReal) x := ?_
        _ = ∫ x in (-B)..B, 2 ^ n * (B - |x|) ^ n / n.factorial := ?_
        _ = 2 ^ n.succ * (∫ x in (0 : ℝ)..B, (B - x) ^ n) / n.factorial := ?_
        _ = 2 ^ n.succ * B ^ n.succ / n.succ.factorial := ?_
      · rw [← (volume_preserving_piFinSuccAboveEquiv (fun _ : Fin (n+1) => ℝ) 0).map_eq,
          integral_map_equiv]
        congr; ext x
        simp_rw [MeasurableEquiv.piFinSuccAboveEquiv_apply, Fin.sum_univ_succ, le_sub_iff_add_le']
        rfl
      · rw [volume_eq_prod]
        rw [integral_prod]
        have : ∀ x : ℝ, MeasurableSet {z : Fin n → ℝ | ∑ i, |z i| ≤ B - |x|} := sorry
        simp_rw [integral_indicator_one (this _)]
        sorry
      · congr
        rw [eq_comm, Set.indicator_eq_self]
        rw [Function.support_subset_iff']
        intro x hx
        rw [Set.mem_Icc, ← abs_le, not_le, ← sub_neg] at hx
        rw [ENNReal.toReal_eq_zero_iff]
        left
        convert MeasureTheory.measure_empty
        rw [Set.eq_empty_iff_forall_not_mem]
        intro z
        rw [Set.mem_setOf_eq, not_le]
        refine lt_of_lt_of_le hx ?_
        refine Finset.sum_nonneg' ?_
        intro _
        exact abs_nonneg _
      · rw [MeasureTheory.integral_indicator measurableSet_Icc]
        rw [set_integral_congr_set_ae Ioc_ae_eq_Icc.symm, ← integral_of_le sorry]
        refine intervalIntegral.integral_congr ?_
        intro x hx
        rw [Set.uIcc_of_le sorry, Set.mem_Icc, ← abs_le, ← sub_nonneg] at hx
        specialize hn (B - |x|) hx
        simp_rw [hn, Nat.cast_pow, Nat.cast_ofNat, toReal_div, toReal_mul, toReal_pow, toReal_ofNat,
          toReal_nat, toReal_ofReal hx]
      · rw [← integral_add_adjacent_intervals (b := 0)]
        conv_lhs =>
          congr
          congr
          ext
          rw [← abs_neg]
        rw [integral_comp_neg (fun x => (2 ^ n) * (B - |x|) ^ n / ↑(Nat.factorial n))]
        rw [neg_zero, neg_neg, ← two_mul, intervalIntegral.integral_div, integral_const_mul]
        rw [mul_div_assoc, ← mul_assoc, mul_div_assoc, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat,
          ← pow_succ]
        congr 2
        rw [intervalIntegral.integral_congr]
        intro x hx

        rw [Set.uIcc_of_le sorry, Set.mem_Icc] at hx
        simp_rw [abs_eq_self.mpr hx.1]
        sorry
        sorry
      · rw [integral_comp_sub_left (fun x => x ^ n) B]
        simp only [Nat.cast_pow, Nat.cast_ofNat, sub_self, sub_zero, integral_pow, ne_eq,
          add_eq_zero, and_false,
          not_false_eq_true, zero_pow', Nat.factorial, Nat.cast_mul, Nat.cast_succ]
        field_simp

#exit

example {n : ℕ} :
    volume {x : (Fin n) → ℝ | ∑ i, |x i| ≤ B} = 2 ^ n * B ^ n / n.factorial := by
  induction n generalizing B with
  | zero =>
      simp only [Nat.zero_eq, Finset.univ_eq_empty, Finset.sum_empty, zero_le_coe, Set.setOf_true,
        volume_pi_isEmpty, pow_zero, Nat.cast_one, coe_one, mul_one, Nat.factorial, div_one]
  | succ n hn =>
      suffices ∫ a, Set.indicator {x | ∑ i, |x i| ≤ ↑B} (1 : (Fin n.succ → ℝ) → ℝ) a =
          2 ^ n.succ * B ^ n.succ / n.succ.factorial by
        sorry
      let g := MeasurableEquiv.piFinSuccAboveEquiv (fun _ : Fin (n+1) => ℝ) 0
      have := volume_preserving_piFinSuccAboveEquiv (fun _ : Fin (n+1) => ℝ) 0
      let s : (Fin n.succ → ℝ) → ℝ := Set.indicator {x | ∑ i, |x i| ≤ ↑B} (1 : (Fin n.succ → ℝ) → ℝ)
      let t : ℝ × (Fin n → ℝ) → ℝ :=
        (fun x => Set.indicator (Set.Icc (-(B : ℝ)) B) 1 x.1) *
          (fun x => Set.indicator {y : (Fin n → ℝ) | ∑ i, |y i| ≤ ↑B - |x.1|} 1 x.2)
      have : ∀ a, s a = t (g a) := sorry
      simp_rw [this]
      rw [← integral_map_equiv]
      have := (volume_preserving_piFinSuccAboveEquiv (fun _ : Fin (n+1) => ℝ) 0).map_eq
      rw [this]

      rw [volume_eq_prod]
      rw [integral_prod]
      simp only [ge_iff_le, neg_le_self_iff, not_le, gt_iff_lt, lt_neg_self_iff, Set.mem_Icc,
        not_and, Set.mem_setOf_eq, Pi.mul_apply, Nat.cast_pow, Nat.cast_ofNat, Nat.factorial,
        Nat.cast_mul, Nat.cast_succ]
      simp_rw [integral_mul_left]
      simp_rw [integral_indicator_one sorry]
      simp_rw [← Set.indicator_mul_left _ _
        (fun a => ENNReal.toReal (volume {y : Fin n → ℝ | ∑ i, |y i| ≤ B - |a|}))]
      simp only [ge_iff_le, neg_le_self_iff, zero_le_one, not_true, gt_iff_lt, lt_neg_self_iff,
        Pi.one_apply, one_mul, Set.mem_Icc, not_and, not_le]
      let T := Set.Ioc (-B) 0 ∪ Set.Ioc 0 B
      have : Set.Icc (-B) B =ᵐ[volume] T := sorry
      rw [MeasureTheory.integral_indicator]
      rw [set_integral_congr_set_ae this]
      rw [integral_union]
      rw [← integral_of_le]
      rw [← integral_of_le]
      nth_rewrite 1 [show (0 : ℝ) = -0 by sorry]
      rw [← intervalIntegral.integral_comp_neg (fun x =>
        ENNReal.toReal (volume {y : Fin n → ℝ | ∑ i, |y i| ≤ B - |x|}))]
      simp only [abs_neg]
      rw [← two_mul]
      conv_lhs =>
        congr
        rfl
        congr
        ext x
        rw [show |x| = x by sorry]
      rw [integral_comp_sub_left (fun x =>
          ENNReal.toReal (volume {y : Fin n → ℝ | ∑ i, |y i| ≤ x})) B]
      simp only [sub_self, sub_zero]
      conv_lhs =>
        congr
        rfl
        congr
        ext x
        rw [hn sorry]
      simp [pow_succ]
      field_simp
      ring
      · exact h
      · rw [@neg_nonpos]
        exact h
      · simp_all only [Nat.cast_pow, Nat.cast_ofNat, MeasurableEquiv.piFinSuccAboveEquiv_apply,
          Fin.zero_succAbove,
          Set.mem_setOf_eq, not_le, ge_iff_le, neg_le_self_iff, not_true, gt_iff_lt, lt_neg_self_iff,
          Set.mem_Icc,
          not_and, Pi.mul_apply, Left.neg_nonpos_iff, Set.Ioc_union_Ioc_eq_Ioc, neg_lt_self_iff,
          not_lt,
          le_neg_self_iff, Left.neg_neg_iff, Left.nonneg_neg_iff, Set.Ioc_disjoint_Ioc_same]
      · exact measurableSet_Ioc
      · sorry
      · sorry
      · exact measurableSet_Icc
      · sorry

#exit
      rw [← lintegral_indicator_one]
      let s : (Fin n.succ → ℝ) → ℝ≥0∞ := Set.indicator {x | ∑ i, ‖x i‖ ≤ 1} (1 : (Fin n.succ → ℝ) → ℝ≥0∞)
      let t : ℝ × (Fin n → ℝ) → ℝ≥0∞ :=
        (fun x => Set.indicator (Set.Icc (-1 : ℝ) 1) 1 x.1) *
          (fun x => Set.indicator {y : (Fin n → ℝ) | ∑ i, ‖y i‖ ≤ 1 - ‖x.1‖} 1 x.2)
      have : ∀ a, s a = t (g a) := sorry
    --  dsimp only at this
      simp_rw [this]
      rw [← lintegral_map_equiv]
      have := (volume_preserving_piFinSuccAboveEquiv (fun _ : Fin (n+1) => ℝ) 0).map_eq
      rw [this]
      rw [volume_eq_prod]
      rw [lintegral_prod]
      -- have : ∀ a, t₀ a = t a := sorry
      have t1 : ∀ C, MeasurableSet {y : Fin n → ℝ | ∑ i : Fin n, ‖y i‖ ≤ C} := sorry
      -- simp_rw [this]
      simp
      simp_rw [lintegral_const_mul _ sorry]
      simp_rw [lintegral_indicator_one sorry]
      conv_lhs =>
        congr
        rfl
        ext x
        rw [← Set.indicator_mul_left _ _ (fun a => volume {y : Fin n → ℝ | ∑ i, |y i| ≤ 1 - |a|})]
      -- dsimp
--      simp_rw [← Set.indicator_mul_left _ _
--        (fun x => ENNReal.ofReal (↑(2 ^ n) * ((B : ℝ) - |x|) ^ n / ↑(Nat.factorial n)))]
      simp only [ge_iff_le, neg_le_self_iff, zero_le_one, not_true, gt_iff_lt, lt_neg_self_iff,
        Pi.one_apply, one_mul, Set.mem_Icc, not_and, not_le]

      rw [lintegral_indicator
        (fun x => volume {y : Fin n → ℝ | ∑ i, |y i| ≤ 1 - |x|})]
      let T := Set.Ico (-1 : ℝ) 0 ∪ Set.Ico (0 : ℝ) 1
      have : Set.Icc (-1 : ℝ) 1 =ᵐ[volume] T := sorry
      rw [set_lintegral_congr this]
      rw [lintegral_union]
      rw [lintegral_coe_eq_integral]
      sorry

#exit
  induction s using Finset.induction with
  | empty =>
      simp
  | insert ha hs =>
      rename_i a s
      rw [← set_lintegral_one]
      have : ∀ x : { x // x ∈ insert a s } → ℝ, ∑ i : { x // x ∈ insert a s }, ‖x i‖ =
          ∑ i in s, ‖x i‖ + x a := by
        sorry
      simp_rw [Finset.sum_insert ha]
      sorry



#exit

  induction n, hn using Nat.le_induction with
  | base =>
      rw [show {x : Fin 1 → ℝ | ∑ i : Fin 1, ‖x i‖ ≤ B} = Metric.closedBall 0 B by
        ext; simp [Pi.norm_def]]
      simp only [zero_le_coe, Real.volume_pi_closedBall, Fintype.card_ofSubsingleton, pow_one,
        Nat.cast_ofNat, Nat.factorial, mul_one, Nat.cast_one, div_one]
  | succ m hm hrec =>
      rw [← set_lintegral_one]
      simp_rw [Fin.sum_univ_add, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]

#exit

theorem aux1_volume_computation (n : ℕ) (hn : 1 ≤ n) :
    volume {x : ((Fin n) → ℝ) | ∑ i, ‖x i‖ ≤ B} = ENNReal.ofReal (2 ^ n * B ^ n / n.factorial) := by
  induction n, hn using Nat.le_induction with
  | base =>
      rw [show {x : Fin 1 → ℝ | ∑ i : Fin 1, ‖x i‖ ≤ B} = Metric.closedBall 0 B by
        ext; simp [Pi.norm_def]]
      simp only [zero_le_coe, Real.volume_pi_closedBall, Fintype.card_ofSubsingleton, pow_one,
        Nat.cast_ofNat, Nat.factorial, mul_one, Nat.cast_one, div_one]
  | succ m hm hrec =>
      rw [← set_lintegral_one, lintegral_indicator]
      simp_rw [Fin.sum_univ_add, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]


#exit

set_option maxHeartbeats 0 in
theorem aux_volume_computation (r1 r2 : ℕ) (h : 1 ≤ r1 + r2) :
  volume {x : ((Fin r1) → ℝ) × ((Fin r2) → ℂ) |
      ∑ i, ‖x.1 i‖ + 2 * ∑ j, ‖x.2 j‖ ≤ B } = vol B r1 r2 := by
  have : ∀ r1, (h1 : 1 ≤ r1) →
        volume {x : ((Fin r1) → ℝ) × ((Fin 0) → ℂ) | ∑ i, ‖x.1 i‖ ≤ B } =
        vol B r1 0 := by
    intro r1 h1
    induction r1, h1 using Nat.le_induction with
    | base =>
        simp
        rw [← set_lintegral_one]
        rw [volume_eq_prod]
        let μ := (restrict (Measure.prod volume volume)
          {x : (Fin 1 → ℝ) × (Fin 0 → ℂ)| |Prod.fst x 0| ≤ B})
        have :  {x : (Fin 1 → ℝ) × (Fin 0 → ℂ)| |Prod.fst x 0| ≤ B} =
            {x : (Fin 1 → ℝ) | |x 0| ≤ B} ×ˢ Set.univ := by
          rw [@Set.prod_eq]
          rw [@Set.preimage_setOf_eq]
          rw [@Set.preimage_univ]
          exact Eq.symm (Set.inter_univ _)
        rw [this]
        rw [← MeasureTheory.Measure.restrict_prod_eq_prod_univ _]
        rw [MeasureTheory.lintegral_prod]
        rw [@lintegral_one]
        simp

        sorry
    | succ => sorry
  induction r2 with
  | zero => sorry
  | succ => sorry



#exit

theorem convex_body_sum_volume :
  volume (convex_body_sum K r c B) =
    2 ^ (Fintype.card {w : InfinitePlace K // IsReal w}) *
    (NNReal.pi / 2) ^ (Fintype.card {w : InfinitePlace K // IsComplex w})
      * B ^ (finrank ℚ K) / (finrank ℚ K).factorial := by
  convert aux_volume_computation r c B (Fintype.card {w : InfinitePlace K // IsReal w})
    (Fintype.card {w : InfinitePlace K // IsComplex w}) ?_
  let e1 : (Fin (Fintype.card {w : InfinitePlace K // InfinitePlace.IsReal w}) → ℝ) ≃ᵐ
      ({w : InfinitePlace K // InfinitePlace.IsReal w} → ℝ) := by
    let e : (Fin (Fintype.card {w : InfinitePlace K // InfinitePlace.IsReal w})) ≃
        {w : InfinitePlace K // InfinitePlace.IsReal w} := by
      exact (Fintype.equivFin { w // InfinitePlace.IsReal w }).symm
    refine @MeasurableEquiv.piCongrRight
      (Fin (Fintype.card {w : InfinitePlace K // InfinitePlace.IsReal w})) (fun _ => ℝ)
        (fun _ => ℝ) _ _ _ _
    sorry
  sorry

end convex_body_sum

end NumberField.mixedEmbedding
