/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.MeasureTheory.Function.AEMeasurableSequence
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Lattice
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.ContinuousFunction.Basic
import Mathlib.Topology.Instances.EReal
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.GDelta
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Semicontinuous
import Mathlib.Topology.Algebra.Order.LeftRightLim


#align_import measure_theory.constructions.borel_space.basic from "leanprover-community/mathlib"@"9f55d0d4363ae59948c33864cbc52e0b12e0e8ce"

/-!
# Borel (measurable) space

## Main definitions

* `borel α` : the least `σ`-algebra that contains all open sets;
* `class BorelSpace` : a space with `TopologicalSpace` and `MeasurableSpace` structures
  such that `‹MeasurableSpace α› = borel α`;
* `class OpensMeasurableSpace` : a space with `TopologicalSpace` and `MeasurableSpace`
  structures such that all open sets are measurable; equivalently, `borel α ≤ ‹MeasurableSpace α›`.
* `BorelSpace` instances on `Empty`, `Unit`, `Bool`, `Nat`, `Int`, `Rat`;
* `MeasurableSpace` and `BorelSpace` instances on `ℝ`, `ℝ≥0`, `ℝ≥0∞`.

## Main statements

* `IsOpen.measurableSet`, `IsClosed.measurableSet`: open and closed sets are measurable;
* `Continuous.measurable` : a continuous function is measurable;
* `Continuous.measurable2` : if `f : α → β` and `g : α → γ` are measurable and `op : β × γ → δ`
  is continuous, then `fun x => op (f x, g y)` is measurable;
* `Measurable.add` etc : dot notation for arithmetic operations on `Measurable` predicates,
  and similarly for `dist` and `edist`;
* `AEMeasurable.add` : similar dot notation for almost everywhere measurable functions;
* `Measurable.ennreal*` : special cases for arithmetic operations on `ℝ≥0∞`.
-/


noncomputable section

open Classical Set Filter MeasureTheory

open Classical BigOperators Topology NNReal ENNReal MeasureTheory

universe u v w x y

variable {α β γ γ₂ δ : Type*} {ι : Sort y} {s t u : Set α}

section movethis

open Filter Set Topology

theorem iInf_Ioi_eq_iInf_rat_gt {f : ℝ → ℝ} (x : ℝ) (hf : BddBelow (f '' Ioi x))
    (hf_mono : Monotone f) : ⨅ r : Ioi x, f r = ⨅ q : { q' : ℚ // x < q' }, f q := by
  refine' le_antisymm _ _
  · have : Nonempty { r' : ℚ // x < ↑r' } := by
      obtain ⟨r, hrx⟩ := exists_rat_gt x
      exact ⟨⟨r, hrx⟩⟩
    refine' le_ciInf fun r => _
    obtain ⟨y, hxy, hyr⟩ := exists_rat_btwn r.prop
    refine' ciInf_set_le hf (hxy.trans _)
    exact_mod_cast hyr
  · refine' le_ciInf fun q => _
    have hq := q.prop
    rw [mem_Ioi] at hq
    obtain ⟨y, hxy, hyq⟩ := exists_rat_btwn hq
    refine' (ciInf_le _ _).trans _
    · refine' ⟨hf.some, fun z => _⟩
      rintro ⟨u, rfl⟩
      suffices hfu : f u ∈ f '' Ioi x
      exact hf.choose_spec hfu
      exact ⟨u, u.prop, rfl⟩
    · exact ⟨y, hxy⟩
    · refine' hf_mono (le_trans _ hyq.le)
      norm_cast
#align infi_Ioi_eq_infi_rat_gt iInf_Ioi_eq_iInf_rat_gt

-- todo after the port: move to topology/algebra/order/left_right_lim
theorem rightLim_eq_of_tendsto {α β : Type _} [LinearOrder α] [TopologicalSpace β]
    [TopologicalSpace α] [OrderTopology α] [T2Space β] {f : α → β} {a : α} {y : β}
    (h : 𝓝[>] a ≠ ⊥) (h' : Tendsto f (𝓝[>] a) (𝓝 y)) : Function.rightLim f a = y :=
  @leftLim_eq_of_tendsto αᵒᵈ _ _ _ _ _ _ f a y h h'
#align right_lim_eq_of_tendsto rightLim_eq_of_tendsto

-- todo after the port: move to topology/algebra/order/left_right_lim
theorem rightLim_eq_sInf {α β : Type _} [LinearOrder α] [TopologicalSpace β]
    [ConditionallyCompleteLinearOrder β] [OrderTopology β] {f : α → β} (hf : Monotone f) {x : α}
    [TopologicalSpace α] [OrderTopology α] (h : 𝓝[>] x ≠ ⊥) :
    Function.rightLim f x = sInf (f '' Ioi x) :=
  rightLim_eq_of_tendsto h (hf.tendsto_nhdsWithin_Ioi x)
#align right_lim_eq_Inf rightLim_eq_sInf

-- todo after the port: move to order/filter/at_top_bot
theorem exists_seq_monotone_tendsto_atTop_atTop (α : Type _) [SemilatticeSup α] [Nonempty α]
    [(atTop : Filter α).IsCountablyGenerated] :
    ∃ xs : ℕ → α, Monotone xs ∧ Tendsto xs atTop atTop := by
  haveI h_ne_bot : (atTop : Filter α).NeBot := atTop_neBot
  obtain ⟨ys, h⟩ := exists_seq_tendsto (atTop : Filter α)
  let xs : ℕ → α := fun n => Finset.sup' (Finset.range (n + 1)) Finset.nonempty_range_succ ys
  have h_mono : Monotone xs := by
    intro i j hij
    rw [Finset.sup'_le_iff]
    intro k hk
    refine' Finset.le_sup'_of_le _ _ le_rfl
    rw [Finset.mem_range] at hk ⊢
    exact hk.trans_le (add_le_add_right hij _)
  refine' ⟨xs, h_mono, _⟩
  · refine' tendsto_atTop_atTop_of_monotone h_mono _
    have : ∀ a : α, ∃ n : ℕ, a ≤ ys n := by
      rw [tendsto_atTop_atTop] at h
      intro a
      obtain ⟨i, hi⟩ := h a
      exact ⟨i, hi i le_rfl⟩
    intro a
    obtain ⟨i, hi⟩ := this a
    refine' ⟨i, hi.trans _⟩
    refine' Finset.le_sup'_of_le _ _ le_rfl
    rw [Finset.mem_range_succ_iff]
#align exists_seq_monotone_tendsto_at_top_at_top exists_seq_monotone_tendsto_atTop_atTop

theorem exists_seq_antitone_tendsto_atTop_atBot (α : Type _) [SemilatticeInf α] [Nonempty α]
    [h2 : (atBot : Filter α).IsCountablyGenerated] :
    ∃ xs : ℕ → α, Antitone xs ∧ Tendsto xs atTop atBot :=
  @exists_seq_monotone_tendsto_atTop_atTop αᵒᵈ _ _ h2
#align exists_seq_antitone_tendsto_at_top_at_bot exists_seq_antitone_tendsto_atTop_atBot

-- todo after the port: move to topology/algebra/order/monotone_convergence
theorem iSup_eq_iSup_subseq_of_antitone {ι₁ ι₂ α : Type _} [Preorder ι₂] [CompleteLattice α]
    {l : Filter ι₁} [l.NeBot] {f : ι₂ → α} {φ : ι₁ → ι₂} (hf : Antitone f)
    (hφ : Tendsto φ l atBot) : ⨆ i, f i = ⨆ i, f (φ i) :=
  le_antisymm
    (iSup_mono' fun i =>
      Exists.imp (fun j (hj : φ j ≤ i) => hf hj) (hφ.eventually <| eventually_le_atBot i).exists)
    (iSup_mono' fun i => ⟨φ i, le_rfl⟩)
#align supr_eq_supr_subseq_of_antitone iSup_eq_iSup_subseq_of_antitone

end movethis

open MeasurableSpace TopologicalSpace

/-- `MeasurableSpace` structure generated by `TopologicalSpace`. -/
def borel (α : Type u) [TopologicalSpace α] : MeasurableSpace α :=
  generateFrom { s : Set α | IsOpen s }
#align borel borel

theorem borel_anti : Antitone (@borel α) := fun _ _ h =>
  MeasurableSpace.generateFrom_le fun _ hs => .basic _ (h _ hs)
#align borel_anti borel_anti

theorem borel_eq_top_of_discrete [TopologicalSpace α] [DiscreteTopology α] : borel α = ⊤ :=
  top_le_iff.1 fun s _ => GenerateMeasurable.basic s (isOpen_discrete s)
#align borel_eq_top_of_discrete borel_eq_top_of_discrete

theorem borel_eq_top_of_countable [TopologicalSpace α] [T1Space α] [Countable α] : borel α = ⊤ := by
  refine' top_le_iff.1 fun s _ => biUnion_of_singleton s ▸ _
  apply MeasurableSet.biUnion s.to_countable
  intro x _
  apply MeasurableSet.of_compl
  apply GenerateMeasurable.basic
  exact isClosed_singleton.isOpen_compl
#align borel_eq_top_of_countable borel_eq_top_of_countable

theorem borel_eq_generateFrom_of_subbasis {s : Set (Set α)} [t : TopologicalSpace α]
    [SecondCountableTopology α] (hs : t = .generateFrom s) : borel α = .generateFrom s :=
  le_antisymm
    (generateFrom_le fun u (hu : t.IsOpen u) => by
      rw [hs] at hu
      induction hu
      case basic u hu => exact GenerateMeasurable.basic u hu
      case univ => exact @MeasurableSet.univ α (generateFrom s)
      case inter s₁ s₂ _ _ hs₁ hs₂ => exact @MeasurableSet.inter α (generateFrom s) _ _ hs₁ hs₂
      case
        sUnion f hf ih =>
        rcases isOpen_sUnion_countable f (by rwa [hs]) with ⟨v, hv, vf, vu⟩
        rw [← vu]
        exact @MeasurableSet.sUnion α (generateFrom s) _ hv fun x xv => ih _ (vf xv))
    (generateFrom_le fun u hu =>
      GenerateMeasurable.basic _ <| show t.IsOpen u by rw [hs]; exact GenerateOpen.basic _ hu)
#align borel_eq_generate_from_of_subbasis borel_eq_generateFrom_of_subbasis

theorem TopologicalSpace.IsTopologicalBasis.borel_eq_generateFrom [TopologicalSpace α]
    [SecondCountableTopology α] {s : Set (Set α)} (hs : IsTopologicalBasis s) :
    borel α = .generateFrom s :=
  borel_eq_generateFrom_of_subbasis hs.eq_generateFrom
#align topological_space.is_topological_basis.borel_eq_generate_from TopologicalSpace.IsTopologicalBasis.borel_eq_generateFrom

theorem isPiSystem_isOpen [TopologicalSpace α] : IsPiSystem (IsOpen : Set α → Prop) :=
  fun _s hs _t ht _ => IsOpen.inter hs ht
#align is_pi_system_is_open isPiSystem_isOpen

theorem borel_eq_generateFrom_isClosed [TopologicalSpace α] :
    borel α = .generateFrom { s | IsClosed s } :=
  le_antisymm
    (generateFrom_le fun _t ht =>
      @MeasurableSet.of_compl α _ (generateFrom { s | IsClosed s })
        (GenerateMeasurable.basic _ <| isClosed_compl_iff.2 ht))
    (generateFrom_le fun _t ht =>
      @MeasurableSet.of_compl α _ (borel α) (GenerateMeasurable.basic _ <| isOpen_compl_iff.2 ht))
#align borel_eq_generate_from_is_closed borel_eq_generateFrom_isClosed

section OrderTopology

variable (α)

variable [TopologicalSpace α] [SecondCountableTopology α] [LinearOrder α] [OrderTopology α]

theorem borel_eq_generateFrom_Iio : borel α = .generateFrom (range Iio) := by
  refine' le_antisymm _ (generateFrom_le _)
  · rw [borel_eq_generateFrom_of_subbasis (@OrderTopology.topology_eq_generate_intervals α _ _ _)]
    letI : MeasurableSpace α := MeasurableSpace.generateFrom (range Iio)
    have H : ∀ a : α, MeasurableSet (Iio a) := fun a => GenerateMeasurable.basic _ ⟨_, rfl⟩
    refine' generateFrom_le _
    rintro _ ⟨a, rfl | rfl⟩ <;> [skip; apply H]
    by_cases h : ∃ a', ∀ b, a < b ↔ a' ≤ b
    · rcases h with ⟨a', ha'⟩
      rw [(_ : Ioi a = (Iio a')ᶜ)]
      · exact (H _).compl
      simp [Set.ext_iff, ha']
    · rcases isOpen_iUnion_countable (fun a' : { a' : α // a < a' } => { b | a'.1 < b }) fun a' =>
          isOpen_lt' _ with ⟨v, ⟨hv⟩, vu⟩
      simp [Set.ext_iff] at vu
      have : Ioi a = ⋃ x : v, (Iio x.1.1)ᶜ := by
        simp [Set.ext_iff]
        refine' fun x => ⟨fun ax => _, fun ⟨a', ⟨h, _⟩, ax⟩ => lt_of_lt_of_le h ax⟩
        rcases (vu x).2 (by
          refine' not_imp_comm.1 (fun h => _) h
          exact ⟨x, fun b =>
            ⟨fun ab => le_of_not_lt fun h' => h ⟨b, ab, h'⟩, lt_of_lt_of_le ax⟩⟩) with ⟨a', h₁, h₂⟩
        · exact ⟨a', h₁, le_of_lt h₂⟩
      rw [this]
      skip
      apply MeasurableSet.iUnion
      exact fun _ => (H _).compl
  · rw [forall_range_iff]
    intro a
    exact GenerateMeasurable.basic _ isOpen_Iio
#align borel_eq_generate_from_Iio borel_eq_generateFrom_Iio

theorem borel_eq_generateFrom_Ioi : borel α = .generateFrom (range Ioi) :=
  @borel_eq_generateFrom_Iio αᵒᵈ _ (by infer_instance : SecondCountableTopology α) _ _
#align borel_eq_generate_from_Ioi borel_eq_generateFrom_Ioi

theorem borel_eq_generateFrom_Iic :
    borel α = MeasurableSpace.generateFrom (range Iic) := by
  rw [borel_eq_generateFrom_Ioi]
  refine' le_antisymm _ _
  · refine' MeasurableSpace.generateFrom_le fun t ht => _
    obtain ⟨u, rfl⟩ := ht
    rw [← compl_Iic]
    exact (MeasurableSpace.measurableSet_generateFrom (mem_range.mpr ⟨u, rfl⟩)).compl
  · refine' MeasurableSpace.generateFrom_le fun t ht => _
    obtain ⟨u, rfl⟩ := ht
    rw [← compl_Ioi]
    exact (MeasurableSpace.measurableSet_generateFrom (mem_range.mpr ⟨u, rfl⟩)).compl
#align borel_eq_generate_from_Iic borel_eq_generateFrom_Iic

theorem borel_eq_generateFrom_Ici : borel α = MeasurableSpace.generateFrom (range Ici) :=
  @borel_eq_generateFrom_Iic αᵒᵈ _ _ _ _
#align borel_eq_generate_from_Ici borel_eq_generateFrom_Ici

end OrderTopology

theorem borel_comap {f : α → β} {t : TopologicalSpace β} :
    @borel α (t.induced f) = (@borel β t).comap f :=
  comap_generateFrom.symm
#align borel_comap borel_comap

theorem Continuous.borel_measurable [TopologicalSpace α] [TopologicalSpace β] {f : α → β}
    (hf : Continuous f) : @Measurable α β (borel α) (borel β) f :=
  Measurable.of_le_map <|
    generateFrom_le fun s hs => GenerateMeasurable.basic (f ⁻¹' s) (hs.preimage hf)
#align continuous.borel_measurable Continuous.borel_measurable

/-- A space with `MeasurableSpace` and `TopologicalSpace` structures such that
all open sets are measurable. -/
class OpensMeasurableSpace (α : Type*) [TopologicalSpace α] [h : MeasurableSpace α] : Prop where
  borel_le : borel α ≤ h
#align opens_measurable_space OpensMeasurableSpace
#align opens_measurable_space.borel_le OpensMeasurableSpace.borel_le

/-- A space with `MeasurableSpace` and `TopologicalSpace` structures such that
the `σ`-algebra of measurable sets is exactly the `σ`-algebra generated by open sets. -/
class BorelSpace (α : Type*) [TopologicalSpace α] [MeasurableSpace α] : Prop where
  measurable_eq : ‹MeasurableSpace α› = borel α
#align borel_space BorelSpace
#align borel_space.measurable_eq BorelSpace.measurable_eq

namespace Mathlib.Tactic.Borelize

open Lean Elab Term Tactic Meta

/-- The behaviour of `borelize α` depends on the existing assumptions on `α`.

- if `α` is a topological space with instances `[MeasurableSpace α] [BorelSpace α]`, then
  `borelize α` replaces the former instance by `borel α`;
- otherwise, `borelize α` adds instances `borel α : MeasurableSpace α` and `⟨rfl⟩ : BorelSpace α`.

Finally, `borelize α β γ` runs `borelize α; borelize β; borelize γ`.
-/
syntax "borelize" (ppSpace colGt term:max)* : tactic

/-- Add instances `borel e : MeasurableSpace e` and `⟨rfl⟩ : BorelSpace e`. -/
def addBorelInstance (e : Expr) : TacticM Unit := do
  let t ← Lean.Elab.Term.exprToSyntax e
  evalTactic <| ← `(tactic|
    refine_lift
      letI : MeasurableSpace $t := borel $t
      haveI : BorelSpace $t := ⟨rfl⟩
      ?_)

/-- Given a type `e`, an assumption `i : MeasurableSpace e`, and an instance `[BorelSpace e]`,
replace `i` with `borel e`. -/
def borelToRefl (e : Expr) (i : FVarId) : TacticM Unit := do
  let t ← Lean.Elab.Term.exprToSyntax e
  evalTactic <| ← `(tactic|
    have := @BorelSpace.measurable_eq $t _ _ _)
  liftMetaTactic fun m => return [← subst m i]
  evalTactic <| ← `(tactic|
    refine_lift
      letI : MeasurableSpace $t := borel $t
      ?_)

/-- Given a type `$t`, if there is an assumption `[i : MeasurableSpace $t]`, then try to prove
`[BorelSpace $t]` and replace `i` with `borel $t`. Otherwise, add instances
`borel $t : MeasurableSpace $t` and `⟨rfl⟩ : BorelSpace $t`. -/
def borelize (t : Term) : TacticM Unit := withMainContext <| do
  let u ← mkFreshLevelMVar
  let e ← withoutRecover <| Tactic.elabTermEnsuringType t (mkSort (mkLevelSucc u))
  let i? ← findLocalDeclWithType? (← mkAppOptM ``MeasurableSpace #[e])
  i?.elim (addBorelInstance e) (borelToRefl e)

elab_rules : tactic
  | `(tactic| borelize $[$t:term]*) => t.forM borelize

end Mathlib.Tactic.Borelize

instance (priority := 100) OrderDual.opensMeasurableSpace {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [h : OpensMeasurableSpace α] : OpensMeasurableSpace αᵒᵈ where
  borel_le := h.borel_le
#align order_dual.opens_measurable_space OrderDual.opensMeasurableSpace

instance (priority := 100) OrderDual.borelSpace {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [h : BorelSpace α] : BorelSpace αᵒᵈ where
  measurable_eq := h.measurable_eq
#align order_dual.borel_space OrderDual.borelSpace

/-- In a `BorelSpace` all open sets are measurable. -/
instance (priority := 100) BorelSpace.opensMeasurable {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [BorelSpace α] : OpensMeasurableSpace α :=
  ⟨ge_of_eq <| BorelSpace.measurable_eq⟩
#align borel_space.opens_measurable BorelSpace.opensMeasurable

instance Subtype.borelSpace {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [hα : BorelSpace α] (s : Set α) : BorelSpace s :=
  ⟨by borelize α; symm; apply borel_comap⟩
#align subtype.borel_space Subtype.borelSpace

instance Subtype.opensMeasurableSpace {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [h : OpensMeasurableSpace α] (s : Set α) : OpensMeasurableSpace s :=
  ⟨by
    rw [borel_comap]
    exact comap_mono h.1⟩
#align subtype.opens_measurable_space Subtype.opensMeasurableSpace

instance (priority := 100) BorelSpace.countablyGenerated {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α] : CountablyGenerated α := by
  obtain ⟨b, bct, -, hb⟩ := exists_countable_basis α
  refine' ⟨⟨b, bct, _⟩⟩
  borelize α
  exact hb.borel_eq_generateFrom
#align borel_space.countably_generated BorelSpace.countablyGenerated

theorem MeasurableSet.induction_on_open [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
    {C : Set α → Prop} (h_open : ∀ U, IsOpen U → C U)
    (h_compl : ∀ t, MeasurableSet t → C t → C tᶜ)
    (h_union :
      ∀ f : ℕ → Set α,
        Pairwise (Disjoint on f) → (∀ i, MeasurableSet (f i)) → (∀ i, C (f i)) → C (⋃ i, f i)) :
    ∀ ⦃t⦄, MeasurableSet t → C t :=
  MeasurableSpace.induction_on_inter BorelSpace.measurable_eq isPiSystem_isOpen
    (h_open _ isOpen_empty) h_open h_compl h_union
#align measurable_set.induction_on_open MeasurableSet.induction_on_open

section

variable [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α] [TopologicalSpace β]
  [MeasurableSpace β] [OpensMeasurableSpace β] [TopologicalSpace γ] [MeasurableSpace γ]
  [BorelSpace γ] [TopologicalSpace γ₂] [MeasurableSpace γ₂] [BorelSpace γ₂] [MeasurableSpace δ]

theorem IsOpen.measurableSet (h : IsOpen s) : MeasurableSet s :=
  OpensMeasurableSpace.borel_le _ <| GenerateMeasurable.basic _ h
#align is_open.measurable_set IsOpen.measurableSet

instance (priority := 500) {s : Set α} [HasCountableSeparatingOn α IsOpen s] :
    HasCountableSeparatingOn α MeasurableSet s :=
  .mono (fun _ ↦ IsOpen.measurableSet) Subset.rfl

@[measurability]
theorem measurableSet_interior : MeasurableSet (interior s) :=
  isOpen_interior.measurableSet
#align measurable_set_interior measurableSet_interior

theorem IsGδ.measurableSet (h : IsGδ s) : MeasurableSet s := by
  rcases h with ⟨S, hSo, hSc, rfl⟩
  exact MeasurableSet.sInter hSc fun t ht => (hSo t ht).measurableSet
set_option linter.uppercaseLean3 false in
#align is_Gδ.measurable_set IsGδ.measurableSet

theorem measurableSet_of_continuousAt {β} [EMetricSpace β] (f : α → β) :
    MeasurableSet { x | ContinuousAt f x } :=
  (isGδ_setOf_continuousAt f).measurableSet
#align measurable_set_of_continuous_at measurableSet_of_continuousAt

theorem IsClosed.measurableSet (h : IsClosed s) : MeasurableSet s :=
  h.isOpen_compl.measurableSet.of_compl
#align is_closed.measurable_set IsClosed.measurableSet

theorem IsCompact.measurableSet [T2Space α] (h : IsCompact s) : MeasurableSet s :=
  h.isClosed.measurableSet
#align is_compact.measurable_set IsCompact.measurableSet

@[measurability]
theorem measurableSet_closure : MeasurableSet (closure s) :=
  isClosed_closure.measurableSet
#align measurable_set_closure measurableSet_closure

theorem measurable_of_isOpen {f : δ → γ} (hf : ∀ s, IsOpen s → MeasurableSet (f ⁻¹' s)) :
    Measurable f := by
  rw [‹BorelSpace γ›.measurable_eq]
  exact measurable_generateFrom hf
#align measurable_of_is_open measurable_of_isOpen

theorem measurable_of_isClosed {f : δ → γ} (hf : ∀ s, IsClosed s → MeasurableSet (f ⁻¹' s)) :
    Measurable f := by
  apply measurable_of_isOpen; intro s hs
  rw [← MeasurableSet.compl_iff, ← preimage_compl]; apply hf; rw [isClosed_compl_iff]; exact hs
#align measurable_of_is_closed measurable_of_isClosed

theorem measurable_of_is_closed' {f : δ → γ}
    (hf : ∀ s, IsClosed s → s.Nonempty → s ≠ univ → MeasurableSet (f ⁻¹' s)) : Measurable f := by
  apply measurable_of_isClosed; intro s hs
  cases' eq_empty_or_nonempty s with h1 h1; · simp [h1]
  by_cases h2 : s = univ; · simp [h2]
  exact hf s hs h1 h2
#align measurable_of_is_closed' measurable_of_is_closed'

instance nhds_isMeasurablyGenerated (a : α) : (𝓝 a).IsMeasurablyGenerated := by
  rw [nhds, iInf_subtype']
  refine' @Filter.iInf_isMeasurablyGenerated α _ _ _ fun i => _
  exact i.2.2.measurableSet.principal_isMeasurablyGenerated
#align nhds_is_measurably_generated nhds_isMeasurablyGenerated

/-- If `s` is a measurable set, then `𝓝[s] a` is a measurably generated filter for
each `a`. This cannot be an `instance` because it depends on a non-instance `hs : MeasurableSet s`.
-/
theorem MeasurableSet.nhdsWithin_isMeasurablyGenerated {s : Set α} (hs : MeasurableSet s) (a : α) :
    (𝓝[s] a).IsMeasurablyGenerated :=
  haveI := hs.principal_isMeasurablyGenerated
  Filter.inf_isMeasurablyGenerated _ _
#align measurable_set.nhds_within_is_measurably_generated MeasurableSet.nhdsWithin_isMeasurablyGenerated

-- see Note [lower instance priority]
instance (priority := 100) OpensMeasurableSpace.toMeasurableSingletonClass [T1Space α] :
    MeasurableSingletonClass α :=
  ⟨fun _ => isClosed_singleton.measurableSet⟩
#align opens_measurable_space.to_measurable_singleton_class OpensMeasurableSpace.toMeasurableSingletonClass

instance Pi.opensMeasurableSpace {ι : Type*} {π : ι → Type*} [Countable ι]
    [t' : ∀ i, TopologicalSpace (π i)] [∀ i, MeasurableSpace (π i)]
    [∀ i, SecondCountableTopology (π i)] [∀ i, OpensMeasurableSpace (π i)] :
    OpensMeasurableSpace (∀ i, π i) := by
  constructor
  have : Pi.topologicalSpace = .generateFrom { t | ∃ (s : ∀ a, Set (π a)) (i : Finset ι),
      (∀ a ∈ i, s a ∈ countableBasis (π a)) ∧ t = pi (↑i) s } := by
    rw [funext fun a => @eq_generateFrom_countableBasis (π a) _ _, pi_generateFrom_eq]
  rw [borel_eq_generateFrom_of_subbasis this]
  apply generateFrom_le
  rintro _ ⟨s, i, hi, rfl⟩
  refine' MeasurableSet.pi i.countable_toSet fun a ha => IsOpen.measurableSet _
  rw [eq_generateFrom_countableBasis (π a)]
  exact .basic _ (hi a ha)
#align pi.opens_measurable_space Pi.opensMeasurableSpace

instance Prod.opensMeasurableSpace [SecondCountableTopology α] [SecondCountableTopology β] :
    OpensMeasurableSpace (α × β) := by
  constructor
  rw [((isBasis_countableBasis α).prod (isBasis_countableBasis β)).borel_eq_generateFrom]
  apply generateFrom_le
  rintro _ ⟨u, v, hu, hv, rfl⟩
  exact (isOpen_of_mem_countableBasis hu).measurableSet.prod
    (isOpen_of_mem_countableBasis hv).measurableSet
#align prod.opens_measurable_space Prod.opensMeasurableSpace

variable {α' : Type*} [TopologicalSpace α'] [MeasurableSpace α']

theorem interior_ae_eq_of_null_frontier {μ : Measure α'} {s : Set α'} (h : μ (frontier s) = 0) :
    interior s =ᵐ[μ] s :=
  interior_subset.eventuallyLE.antisymm <| subset_closure.eventuallyLE.trans (ae_le_set.2 h)
#align interior_ae_eq_of_null_frontier interior_ae_eq_of_null_frontier

theorem measure_interior_of_null_frontier {μ : Measure α'} {s : Set α'} (h : μ (frontier s) = 0) :
    μ (interior s) = μ s :=
  measure_congr (interior_ae_eq_of_null_frontier h)
#align measure_interior_of_null_frontier measure_interior_of_null_frontier

theorem nullMeasurableSet_of_null_frontier {s : Set α} {μ : Measure α} (h : μ (frontier s) = 0) :
    NullMeasurableSet s μ :=
  ⟨interior s, isOpen_interior.measurableSet, (interior_ae_eq_of_null_frontier h).symm⟩
#align null_measurable_set_of_null_frontier nullMeasurableSet_of_null_frontier

theorem closure_ae_eq_of_null_frontier {μ : Measure α'} {s : Set α'} (h : μ (frontier s) = 0) :
    closure s =ᵐ[μ] s :=
  ((ae_le_set.2 h).trans interior_subset.eventuallyLE).antisymm <| subset_closure.eventuallyLE
#align closure_ae_eq_of_null_frontier closure_ae_eq_of_null_frontier

theorem measure_closure_of_null_frontier {μ : Measure α'} {s : Set α'} (h : μ (frontier s) = 0) :
    μ (closure s) = μ s :=
  measure_congr (closure_ae_eq_of_null_frontier h)
#align measure_closure_of_null_frontier measure_closure_of_null_frontier

section Preorder

variable [Preorder α] [OrderClosedTopology α] {a b x : α}

@[simp, measurability]
theorem measurableSet_Ici : MeasurableSet (Ici a) :=
  isClosed_Ici.measurableSet
#align measurable_set_Ici measurableSet_Ici

@[simp, measurability]
theorem measurableSet_Iic : MeasurableSet (Iic a) :=
  isClosed_Iic.measurableSet
#align measurable_set_Iic measurableSet_Iic

@[simp, measurability]
theorem measurableSet_Icc : MeasurableSet (Icc a b) :=
  isClosed_Icc.measurableSet
#align measurable_set_Icc measurableSet_Icc

instance nhdsWithin_Ici_isMeasurablyGenerated : (𝓝[Ici b] a).IsMeasurablyGenerated :=
  measurableSet_Ici.nhdsWithin_isMeasurablyGenerated _
#align nhds_within_Ici_is_measurably_generated nhdsWithin_Ici_isMeasurablyGenerated

instance nhdsWithin_Iic_isMeasurablyGenerated : (𝓝[Iic b] a).IsMeasurablyGenerated :=
  measurableSet_Iic.nhdsWithin_isMeasurablyGenerated _
#align nhds_within_Iic_is_measurably_generated nhdsWithin_Iic_isMeasurablyGenerated

instance nhdsWithin_Icc_isMeasurablyGenerated : IsMeasurablyGenerated (𝓝[Icc a b] x) := by
  rw [← Ici_inter_Iic, nhdsWithin_inter]
  infer_instance
#align nhds_within_Icc_is_measurably_generated nhdsWithin_Icc_isMeasurablyGenerated

instance atTop_isMeasurablyGenerated : (Filter.atTop : Filter α).IsMeasurablyGenerated :=
  @Filter.iInf_isMeasurablyGenerated _ _ _ _ fun a =>
    (measurableSet_Ici : MeasurableSet (Ici a)).principal_isMeasurablyGenerated
#align at_top_is_measurably_generated atTop_isMeasurablyGenerated

instance atBot_isMeasurablyGenerated : (Filter.atBot : Filter α).IsMeasurablyGenerated :=
  @Filter.iInf_isMeasurablyGenerated _ _ _ _ fun a =>
    (measurableSet_Iic : MeasurableSet (Iic a)).principal_isMeasurablyGenerated
#align at_bot_is_measurably_generated atBot_isMeasurablyGenerated

end Preorder

section PartialOrder

variable [PartialOrder α] [OrderClosedTopology α] [SecondCountableTopology α] {a b : α}

@[measurability]
theorem measurableSet_le' : MeasurableSet { p : α × α | p.1 ≤ p.2 } :=
  OrderClosedTopology.isClosed_le'.measurableSet
#align measurable_set_le' measurableSet_le'

@[measurability]
theorem measurableSet_le {f g : δ → α} (hf : Measurable f) (hg : Measurable g) :
    MeasurableSet { a | f a ≤ g a } :=
  hf.prod_mk hg measurableSet_le'
#align measurable_set_le measurableSet_le

end PartialOrder

section LinearOrder

variable [LinearOrder α] [OrderClosedTopology α] {a b x : α}

-- we open this locale only here to avoid issues with list being treated as intervals above
open Interval

@[simp, measurability]
theorem measurableSet_Iio : MeasurableSet (Iio a) :=
  isOpen_Iio.measurableSet
#align measurable_set_Iio measurableSet_Iio

@[simp, measurability]
theorem measurableSet_Ioi : MeasurableSet (Ioi a) :=
  isOpen_Ioi.measurableSet
#align measurable_set_Ioi measurableSet_Ioi

@[simp, measurability]
theorem measurableSet_Ioo : MeasurableSet (Ioo a b) :=
  isOpen_Ioo.measurableSet
#align measurable_set_Ioo measurableSet_Ioo

@[simp, measurability]
theorem measurableSet_Ioc : MeasurableSet (Ioc a b) :=
  measurableSet_Ioi.inter measurableSet_Iic
#align measurable_set_Ioc measurableSet_Ioc

@[simp, measurability]
theorem measurableSet_Ico : MeasurableSet (Ico a b) :=
  measurableSet_Ici.inter measurableSet_Iio
#align measurable_set_Ico measurableSet_Ico

instance nhdsWithin_Ioi_isMeasurablyGenerated : (𝓝[Ioi b] a).IsMeasurablyGenerated :=
  measurableSet_Ioi.nhdsWithin_isMeasurablyGenerated _
#align nhds_within_Ioi_is_measurably_generated nhdsWithin_Ioi_isMeasurablyGenerated

instance nhdsWithin_Iio_isMeasurablyGenerated : (𝓝[Iio b] a).IsMeasurablyGenerated :=
  measurableSet_Iio.nhdsWithin_isMeasurablyGenerated _
#align nhds_within_Iio_is_measurably_generated nhdsWithin_Iio_isMeasurablyGenerated

instance nhdsWithin_uIcc_isMeasurablyGenerated : IsMeasurablyGenerated (𝓝[[[a, b]]] x) :=
  nhdsWithin_Icc_isMeasurablyGenerated
#align nhds_within_uIcc_is_measurably_generated nhdsWithin_uIcc_isMeasurablyGenerated

@[measurability]
theorem measurableSet_lt' [SecondCountableTopology α] : MeasurableSet { p : α × α | p.1 < p.2 } :=
  (isOpen_lt continuous_fst continuous_snd).measurableSet
#align measurable_set_lt' measurableSet_lt'

@[measurability]
theorem measurableSet_lt [SecondCountableTopology α] {f g : δ → α} (hf : Measurable f)
    (hg : Measurable g) : MeasurableSet { a | f a < g a } :=
  hf.prod_mk hg measurableSet_lt'
#align measurable_set_lt measurableSet_lt

theorem nullMeasurableSet_lt [SecondCountableTopology α] {μ : Measure δ} {f g : δ → α}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) : NullMeasurableSet { a | f a < g a } μ :=
  (hf.prod_mk hg).nullMeasurable measurableSet_lt'
#align null_measurable_set_lt nullMeasurableSet_lt

theorem Set.OrdConnected.measurableSet (h : OrdConnected s) : MeasurableSet s := by
  let u := ⋃ (x ∈ s) (y ∈ s), Ioo x y
  have huopen : IsOpen u := isOpen_biUnion fun _ _ => isOpen_biUnion fun _ _ => isOpen_Ioo
  have humeas : MeasurableSet u := huopen.measurableSet
  have hfinite : (s \ u).Finite := s.finite_diff_iUnion_Ioo
  have : u ⊆ s := iUnion₂_subset fun x hx => iUnion₂_subset fun y hy =>
    Ioo_subset_Icc_self.trans (h.out hx hy)
  rw [← union_diff_cancel this]
  exact humeas.union hfinite.measurableSet
#align set.ord_connected.measurable_set Set.OrdConnected.measurableSet

theorem IsPreconnected.measurableSet (h : IsPreconnected s) : MeasurableSet s :=
  h.ordConnected.measurableSet
#align is_preconnected.measurable_set IsPreconnected.measurableSet

theorem generateFrom_Ico_mem_le_borel {α : Type*} [TopologicalSpace α] [LinearOrder α]
    [OrderClosedTopology α] (s t : Set α) :
    MeasurableSpace.generateFrom { S | ∃ l ∈ s, ∃ u ∈ t, l < u ∧ Ico l u = S }
      ≤ borel α := by
  apply generateFrom_le
  borelize α
  rintro _ ⟨a, -, b, -, -, rfl⟩
  exact measurableSet_Ico
#align generate_from_Ico_mem_le_borel generateFrom_Ico_mem_le_borel

theorem Dense.borel_eq_generateFrom_Ico_mem_aux {α : Type*} [TopologicalSpace α] [LinearOrder α]
    [OrderTopology α] [SecondCountableTopology α] {s : Set α} (hd : Dense s)
    (hbot : ∀ x, IsBot x → x ∈ s) (hIoo : ∀ x y : α, x < y → Ioo x y = ∅ → y ∈ s) :
    borel α = .generateFrom { S : Set α | ∃ l ∈ s, ∃ u ∈ s, l < u ∧ Ico l u = S } := by
  set S : Set (Set α) := { S | ∃ l ∈ s, ∃ u ∈ s, l < u ∧ Ico l u = S }
  refine' le_antisymm _ (generateFrom_Ico_mem_le_borel _ _)
  letI : MeasurableSpace α := generateFrom S
  rw [borel_eq_generateFrom_Iio]
  refine' generateFrom_le (forall_range_iff.2 fun a => _)
  rcases hd.exists_countable_dense_subset_bot_top with ⟨t, hts, hc, htd, htb, -⟩
  by_cases ha : ∀ b < a, (Ioo b a).Nonempty
  · convert_to MeasurableSet (⋃ (l ∈ t) (u ∈ t) (_ : l < u) (_ : u ≤ a), Ico l u)
    · ext y
      simp only [mem_iUnion, mem_Iio, mem_Ico]
      constructor
      · intro hy
        rcases htd.exists_le' (fun b hb => htb _ hb (hbot b hb)) y with ⟨l, hlt, hly⟩
        rcases htd.exists_mem_open isOpen_Ioo (ha y hy) with ⟨u, hut, hyu, hua⟩
        exact ⟨l, hlt, u, hut, hly.trans_lt hyu, hua.le, hly, hyu⟩
      · rintro ⟨l, -, u, -, -, hua, -, hyu⟩
        exact hyu.trans_le hua
    · refine' MeasurableSet.biUnion hc fun a ha => MeasurableSet.biUnion hc fun b hb => _
      refine' MeasurableSet.iUnion fun hab => MeasurableSet.iUnion fun _ => _
      exact .basic _ ⟨a, hts ha, b, hts hb, hab, mem_singleton _⟩
  · simp only [not_forall, not_nonempty_iff_eq_empty] at ha
    replace ha : a ∈ s := hIoo ha.choose a ha.choose_spec.fst ha.choose_spec.snd
    convert_to MeasurableSet (⋃ (l ∈ t) (_ : l < a), Ico l a)
    · symm
      simp only [← Ici_inter_Iio, ← iUnion_inter, inter_eq_right_iff_subset, subset_def, mem_iUnion,
        mem_Ici, mem_Iio]
      intro x hx
      rcases htd.exists_le' (fun b hb => htb _ hb (hbot b hb)) x with ⟨z, hzt, hzx⟩
      exact ⟨z, hzt, hzx.trans_lt hx, hzx⟩
    · refine' .biUnion hc fun x hx => MeasurableSet.iUnion fun hlt => _
      exact .basic _ ⟨x, hts hx, a, ha, hlt, mem_singleton _⟩
#align dense.borel_eq_generate_from_Ico_mem_aux Dense.borel_eq_generateFrom_Ico_mem_aux

theorem Dense.borel_eq_generateFrom_Ico_mem {α : Type*} [TopologicalSpace α] [LinearOrder α]
    [OrderTopology α] [SecondCountableTopology α] [DenselyOrdered α] [NoMinOrder α] {s : Set α}
    (hd : Dense s) :
    borel α = .generateFrom { S : Set α | ∃ l ∈ s, ∃ u ∈ s, l < u ∧ Ico l u = S } :=
  hd.borel_eq_generateFrom_Ico_mem_aux (by simp) fun x y hxy H =>
    ((nonempty_Ioo.2 hxy).ne_empty H).elim
#align dense.borel_eq_generate_from_Ico_mem Dense.borel_eq_generateFrom_Ico_mem

theorem borel_eq_generateFrom_Ico (α : Type*) [TopologicalSpace α] [SecondCountableTopology α]
    [LinearOrder α] [OrderTopology α] :
    borel α = .generateFrom { S : Set α | ∃ (l u : α), l < u ∧ Ico l u = S } := by
  simpa only [exists_prop, mem_univ, true_and_iff] using
    (@dense_univ α _).borel_eq_generateFrom_Ico_mem_aux (fun _ _ => mem_univ _) fun _ _ _ _ =>
      mem_univ _
#align borel_eq_generate_from_Ico borel_eq_generateFrom_Ico

theorem Dense.borel_eq_generateFrom_Ioc_mem_aux {α : Type*} [TopologicalSpace α] [LinearOrder α]
    [OrderTopology α] [SecondCountableTopology α] {s : Set α} (hd : Dense s)
    (hbot : ∀ x, IsTop x → x ∈ s) (hIoo : ∀ x y : α, x < y → Ioo x y = ∅ → x ∈ s) :
    borel α = .generateFrom { S : Set α | ∃ l ∈ s, ∃ u ∈ s, l < u ∧ Ioc l u = S } := by
  convert hd.orderDual.borel_eq_generateFrom_Ico_mem_aux hbot fun x y hlt he => hIoo y x hlt _
    using 2
  · ext s
    constructor <;> rintro ⟨l, hl, u, hu, hlt, rfl⟩
    exacts [⟨u, hu, l, hl, hlt, dual_Ico⟩, ⟨u, hu, l, hl, hlt, dual_Ioc⟩]
  · erw [dual_Ioo]
    exact he
#align dense.borel_eq_generate_from_Ioc_mem_aux Dense.borel_eq_generateFrom_Ioc_mem_aux

theorem Dense.borel_eq_generateFrom_Ioc_mem {α : Type*} [TopologicalSpace α] [LinearOrder α]
    [OrderTopology α] [SecondCountableTopology α] [DenselyOrdered α] [NoMaxOrder α] {s : Set α}
    (hd : Dense s) :
    borel α = .generateFrom { S : Set α | ∃ l ∈ s, ∃ u ∈ s, l < u ∧ Ioc l u = S } :=
  hd.borel_eq_generateFrom_Ioc_mem_aux (by simp) fun x y hxy H =>
    ((nonempty_Ioo.2 hxy).ne_empty H).elim
#align dense.borel_eq_generate_from_Ioc_mem Dense.borel_eq_generateFrom_Ioc_mem

theorem borel_eq_generateFrom_Ioc (α : Type*) [TopologicalSpace α] [SecondCountableTopology α]
    [LinearOrder α] [OrderTopology α] :
    borel α = .generateFrom { S : Set α | ∃ l u, l < u ∧ Ioc l u = S } := by
  simpa only [exists_prop, mem_univ, true_and_iff] using
    (@dense_univ α _).borel_eq_generateFrom_Ioc_mem_aux (fun _ _ => mem_univ _) fun _ _ _ _ =>
      mem_univ _
#align borel_eq_generate_from_Ioc borel_eq_generateFrom_Ioc

namespace MeasureTheory.Measure

/-- Two finite measures on a Borel space are equal if they agree on all closed-open intervals.  If
`α` is a conditionally complete linear order with no top element,
`MeasureTheory.Measure.ext_of_Ico` is an extensionality lemma with weaker assumptions on `μ` and
`ν`. -/
theorem ext_of_Ico_finite {α : Type*} [TopologicalSpace α] {m : MeasurableSpace α}
    [SecondCountableTopology α] [LinearOrder α] [OrderTopology α] [BorelSpace α] (μ ν : Measure α)
    [IsFiniteMeasure μ] (hμν : μ univ = ν univ) (h : ∀ ⦃a b⦄, a < b → μ (Ico a b) = ν (Ico a b)) :
    μ = ν := by
  refine'
    ext_of_generate_finite _ (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Ico α))
      (isPiSystem_Ico (id : α → α) id) _ hμν
  · rintro - ⟨a, b, hlt, rfl⟩
    exact h hlt
#align measure_theory.measure.ext_of_Ico_finite MeasureTheory.Measure.ext_of_Ico_finite

/-- Two finite measures on a Borel space are equal if they agree on all open-closed intervals.  If
`α` is a conditionally complete linear order with no top element,
`MeasureTheory.Measure.ext_of_Ioc` is an extensionality lemma with weaker assumptions on `μ` and
`ν`. -/
theorem ext_of_Ioc_finite {α : Type*} [TopologicalSpace α] {m : MeasurableSpace α}
    [SecondCountableTopology α] [LinearOrder α] [OrderTopology α] [BorelSpace α] (μ ν : Measure α)
    [IsFiniteMeasure μ] (hμν : μ univ = ν univ) (h : ∀ ⦃a b⦄, a < b → μ (Ioc a b) = ν (Ioc a b)) :
    μ = ν := by
  refine' @ext_of_Ico_finite αᵒᵈ _ _ _ _ _ ‹_› μ ν _ hμν fun a b hab => _
  erw [dual_Ico (α := α)]
  exact h hab
#align measure_theory.measure.ext_of_Ioc_finite MeasureTheory.Measure.ext_of_Ioc_finite

/-- Two measures which are finite on closed-open intervals are equal if the agree on all
closed-open intervals. -/
theorem ext_of_Ico' {α : Type*} [TopologicalSpace α] {m : MeasurableSpace α}
    [SecondCountableTopology α] [LinearOrder α] [OrderTopology α] [BorelSpace α] [NoMaxOrder α]
    (μ ν : Measure α) (hμ : ∀ ⦃a b⦄, a < b → μ (Ico a b) ≠ ∞)
    (h : ∀ ⦃a b⦄, a < b → μ (Ico a b) = ν (Ico a b)) : μ = ν := by
  rcases exists_countable_dense_bot_top α with ⟨s, hsc, hsd, hsb, _⟩
  have : (⋃ (l ∈ s) (u ∈ s) (_ : l < u), {Ico l u} : Set (Set α)).Countable :=
    hsc.biUnion fun l _ => hsc.biUnion fun u _ => countable_iUnion fun _ => countable_singleton _
  simp only [← setOf_eq_eq_singleton, ← setOf_exists] at this
  refine'
    Measure.ext_of_generateFrom_of_cover_subset
      (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Ico α)) (isPiSystem_Ico id id) _ this
      _ _ _
  · rintro _ ⟨l, -, u, -, h, rfl⟩
    exact ⟨l, u, h, rfl⟩
  · refine' sUnion_eq_univ_iff.2 fun x => _
    rcases hsd.exists_le' hsb x with ⟨l, hls, hlx⟩
    rcases hsd.exists_gt x with ⟨u, hus, hxu⟩
    exact ⟨_, ⟨l, hls, u, hus, hlx.trans_lt hxu, rfl⟩, hlx, hxu⟩
  · rintro _ ⟨l, -, u, -, hlt, rfl⟩
    exact hμ hlt
  · rintro _ ⟨l, u, hlt, rfl⟩
    exact h hlt
#align measure_theory.measure.ext_of_Ico' MeasureTheory.Measure.ext_of_Ico'

/-- Two measures which are finite on closed-open intervals are equal if the agree on all
open-closed intervals. -/
theorem ext_of_Ioc' {α : Type*} [TopologicalSpace α] {m : MeasurableSpace α}
    [SecondCountableTopology α] [LinearOrder α] [OrderTopology α] [BorelSpace α] [NoMinOrder α]
    (μ ν : Measure α) (hμ : ∀ ⦃a b⦄, a < b → μ (Ioc a b) ≠ ∞)
    (h : ∀ ⦃a b⦄, a < b → μ (Ioc a b) = ν (Ioc a b)) : μ = ν := by
  refine' @ext_of_Ico' αᵒᵈ _ _ _ _ _ ‹_› _ μ ν _ _ <;> intro a b hab <;> erw [dual_Ico (α := α)]
  exacts [hμ hab, h hab]
#align measure_theory.measure.ext_of_Ioc' MeasureTheory.Measure.ext_of_Ioc'

/-- Two measures which are finite on closed-open intervals are equal if the agree on all
closed-open intervals. -/
theorem ext_of_Ico {α : Type*} [TopologicalSpace α] {_m : MeasurableSpace α}
    [SecondCountableTopology α] [ConditionallyCompleteLinearOrder α] [OrderTopology α]
    [BorelSpace α] [NoMaxOrder α] (μ ν : Measure α) [IsLocallyFiniteMeasure μ]
    (h : ∀ ⦃a b⦄, a < b → μ (Ico a b) = ν (Ico a b)) : μ = ν :=
  μ.ext_of_Ico' ν (fun _ _ _ => measure_Ico_lt_top.ne) h
#align measure_theory.measure.ext_of_Ico MeasureTheory.Measure.ext_of_Ico

/-- Two measures which are finite on closed-open intervals are equal if the agree on all
open-closed intervals. -/
theorem ext_of_Ioc {α : Type*} [TopologicalSpace α] {_m : MeasurableSpace α}
    [SecondCountableTopology α] [ConditionallyCompleteLinearOrder α] [OrderTopology α]
    [BorelSpace α] [NoMinOrder α] (μ ν : Measure α) [IsLocallyFiniteMeasure μ]
    (h : ∀ ⦃a b⦄, a < b → μ (Ioc a b) = ν (Ioc a b)) : μ = ν :=
  μ.ext_of_Ioc' ν (fun _ _ _ => measure_Ioc_lt_top.ne) h
#align measure_theory.measure.ext_of_Ioc MeasureTheory.Measure.ext_of_Ioc

/-- Two finite measures on a Borel space are equal if they agree on all left-infinite right-closed
intervals. -/
theorem ext_of_Iic {α : Type*} [TopologicalSpace α] {m : MeasurableSpace α}
    [SecondCountableTopology α] [LinearOrder α] [OrderTopology α] [BorelSpace α] (μ ν : Measure α)
    [IsFiniteMeasure μ] (h : ∀ a, μ (Iic a) = ν (Iic a)) : μ = ν := by
  refine' ext_of_Ioc_finite μ ν _ fun a b hlt => _
  · rcases exists_countable_dense_bot_top α with ⟨s, hsc, hsd, -, hst⟩
    have : DirectedOn (· ≤ ·) s := directedOn_iff_directed.2 (directed_of_sup fun _ _ => id)
    simp only [← biSup_measure_Iic hsc (hsd.exists_ge' hst) this, h]
  rw [← Iic_diff_Iic, measure_diff (Iic_subset_Iic.2 hlt.le) measurableSet_Iic,
    measure_diff (Iic_subset_Iic.2 hlt.le) measurableSet_Iic, h a, h b]
  · rw [← h a]
    exact (measure_lt_top μ _).ne
  · exact (measure_lt_top μ _).ne
#align measure_theory.measure.ext_of_Iic MeasureTheory.Measure.ext_of_Iic

/-- Two finite measures on a Borel space are equal if they agree on all left-closed right-infinite
intervals. -/
theorem ext_of_Ici {α : Type*} [TopologicalSpace α] {m : MeasurableSpace α}
    [SecondCountableTopology α] [LinearOrder α] [OrderTopology α] [BorelSpace α] (μ ν : Measure α)
    [IsFiniteMeasure μ] (h : ∀ a, μ (Ici a) = ν (Ici a)) : μ = ν :=
  @ext_of_Iic αᵒᵈ _ _ _ _ _ ‹_› _ _ _ h
#align measure_theory.measure.ext_of_Ici MeasureTheory.Measure.ext_of_Ici

end MeasureTheory.Measure

end LinearOrder

section LinearOrder

variable [LinearOrder α] [OrderClosedTopology α] {a b : α}

@[measurability]
theorem measurableSet_uIcc : MeasurableSet (uIcc a b) :=
  measurableSet_Icc
#align measurable_set_uIcc measurableSet_uIcc

@[measurability]
theorem measurableSet_uIoc : MeasurableSet (uIoc a b) :=
  measurableSet_Ioc
#align measurable_set_uIoc measurableSet_uIoc

variable [SecondCountableTopology α]

@[measurability]
theorem Measurable.max {f g : δ → α} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a => max (f a) (g a) := by
  simpa only [max_def'] using hf.piecewise (measurableSet_le hg hf) hg
#align measurable.max Measurable.max

@[measurability]
nonrec theorem AEMeasurable.max {f g : δ → α} {μ : Measure δ} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) : AEMeasurable (fun a => max (f a) (g a)) μ :=
  ⟨fun a => max (hf.mk f a) (hg.mk g a), hf.measurable_mk.max hg.measurable_mk,
    EventuallyEq.comp₂ hf.ae_eq_mk _ hg.ae_eq_mk⟩
#align ae_measurable.max AEMeasurable.max

@[measurability]
theorem Measurable.min {f g : δ → α} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a => min (f a) (g a) := by
  simpa only [min_def] using hf.piecewise (measurableSet_le hf hg) hg
#align measurable.min Measurable.min

@[measurability]
nonrec theorem AEMeasurable.min {f g : δ → α} {μ : Measure δ} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) : AEMeasurable (fun a => min (f a) (g a)) μ :=
  ⟨fun a => min (hf.mk f a) (hg.mk g a), hf.measurable_mk.min hg.measurable_mk,
    EventuallyEq.comp₂ hf.ae_eq_mk _ hg.ae_eq_mk⟩
#align ae_measurable.min AEMeasurable.min

end LinearOrder

/-- A continuous function from an `OpensMeasurableSpace` to a `BorelSpace`
is measurable. -/
theorem Continuous.measurable {f : α → γ} (hf : Continuous f) : Measurable f :=
  hf.borel_measurable.mono OpensMeasurableSpace.borel_le (le_of_eq <| BorelSpace.measurable_eq)
#align continuous.measurable Continuous.measurable

/-- A continuous function from an `OpensMeasurableSpace` to a `BorelSpace`
is ae-measurable. -/
theorem Continuous.aemeasurable {f : α → γ} (h : Continuous f) {μ : Measure α} : AEMeasurable f μ :=
  h.measurable.aemeasurable
#align continuous.ae_measurable Continuous.aemeasurable

theorem ClosedEmbedding.measurable {f : α → γ} (hf : ClosedEmbedding f) : Measurable f :=
  hf.continuous.measurable
#align closed_embedding.measurable ClosedEmbedding.measurable

/-- If a function is defined piecewise in terms of functions which are continuous on their
respective pieces, then it is measurable. -/
theorem ContinuousOn.measurable_piecewise {f g : α → γ} {s : Set α} [∀ j : α, Decidable (j ∈ s)]
    (hf : ContinuousOn f s) (hg : ContinuousOn g sᶜ) (hs : MeasurableSet s) :
    Measurable (s.piecewise f g) := by
  refine' measurable_of_isOpen fun t ht => _
  rw [piecewise_preimage, Set.ite]
  apply MeasurableSet.union
  · rcases _root_.continuousOn_iff'.1 hf t ht with ⟨u, u_open, hu⟩
    rw [hu]
    exact u_open.measurableSet.inter hs
  · rcases _root_.continuousOn_iff'.1 hg t ht with ⟨u, u_open, hu⟩
    rw [diff_eq_compl_inter, inter_comm, hu]
    exact u_open.measurableSet.inter hs.compl
#align continuous_on.measurable_piecewise ContinuousOn.measurable_piecewise

@[to_additive]
instance (priority := 100) ContinuousMul.measurableMul [Mul γ] [ContinuousMul γ] :
    MeasurableMul γ where
  measurable_const_mul _ := (continuous_const.mul continuous_id).measurable
  measurable_mul_const _ := (continuous_id.mul continuous_const).measurable
#align has_continuous_mul.has_measurable_mul ContinuousMul.measurableMul
#align has_continuous_add.has_measurable_add ContinuousAdd.measurableAdd

instance (priority := 100) ContinuousSub.measurableSub [Sub γ] [ContinuousSub γ] :
    MeasurableSub γ where
  measurable_const_sub _ := (continuous_const.sub continuous_id).measurable
  measurable_sub_const _ := (continuous_id.sub continuous_const).measurable
#align has_continuous_sub.has_measurable_sub ContinuousSub.measurableSub

@[to_additive]
instance (priority := 100) TopologicalGroup.measurableInv [Group γ] [TopologicalGroup γ] :
    MeasurableInv γ :=
  ⟨continuous_inv.measurable⟩
#align topological_group.has_measurable_inv TopologicalGroup.measurableInv
#align topological_add_group.has_measurable_neg TopologicalAddGroup.measurableNeg

instance (priority := 100) ContinuousSMul.measurableSMul {M α} [TopologicalSpace M]
    [TopologicalSpace α] [MeasurableSpace M] [MeasurableSpace α] [OpensMeasurableSpace M]
    [BorelSpace α] [SMul M α] [ContinuousSMul M α] : MeasurableSMul M α :=
  ⟨fun _ => (continuous_const_smul _).measurable, fun _ =>
    (continuous_id.smul continuous_const).measurable⟩
#align has_continuous_smul.has_measurable_smul ContinuousSMul.measurableSMul

section Lattice

instance (priority := 100) ContinuousSup.measurableSup [Sup γ] [ContinuousSup γ] :
    MeasurableSup γ where
  measurable_const_sup _ := (continuous_const.sup continuous_id).measurable
  measurable_sup_const _ := (continuous_id.sup continuous_const).measurable
#align has_continuous_sup.has_measurable_sup ContinuousSup.measurableSup

instance (priority := 100) ContinuousSup.measurableSup₂ [SecondCountableTopology γ] [Sup γ]
    [ContinuousSup γ] : MeasurableSup₂ γ :=
  ⟨continuous_sup.measurable⟩
#align has_continuous_sup.has_measurable_sup₂ ContinuousSup.measurableSup₂

instance (priority := 100) ContinuousInf.measurableInf [Inf γ] [ContinuousInf γ] :
    MeasurableInf γ where
  measurable_const_inf _ := (continuous_const.inf continuous_id).measurable
  measurable_inf_const _ := (continuous_id.inf continuous_const).measurable
#align has_continuous_inf.has_measurable_inf ContinuousInf.measurableInf

instance (priority := 100) ContinuousInf.measurableInf₂ [SecondCountableTopology γ] [Inf γ]
    [ContinuousInf γ] : MeasurableInf₂ γ :=
  ⟨continuous_inf.measurable⟩
#align has_continuous_inf.has_measurable_inf₂ ContinuousInf.measurableInf₂

end Lattice

section Homeomorph

@[measurability]
protected theorem Homeomorph.measurable (h : α ≃ₜ γ) : Measurable h :=
  h.continuous.measurable
#align homeomorph.measurable Homeomorph.measurable

/-- A homeomorphism between two Borel spaces is a measurable equivalence.-/
def Homeomorph.toMeasurableEquiv (h : γ ≃ₜ γ₂) : γ ≃ᵐ γ₂ where
  measurable_toFun := h.measurable
  measurable_invFun := h.symm.measurable
  toEquiv := h.toEquiv
#align homeomorph.to_measurable_equiv Homeomorph.toMeasurableEquiv

@[simp]
theorem Homeomorph.toMeasurableEquiv_coe (h : γ ≃ₜ γ₂) : (h.toMeasurableEquiv : γ → γ₂) = h :=
  rfl
#align homeomorph.to_measurable_equiv_coe Homeomorph.toMeasurableEquiv_coe

@[simp]
theorem Homeomorph.toMeasurableEquiv_symm_coe (h : γ ≃ₜ γ₂) :
    (h.toMeasurableEquiv.symm : γ₂ → γ) = h.symm :=
  rfl
#align homeomorph.to_measurable_equiv_symm_coe Homeomorph.toMeasurableEquiv_symm_coe

end Homeomorph

@[measurability]
theorem ContinuousMap.measurable (f : C(α, γ)) : Measurable f :=
  f.continuous.measurable
#align continuous_map.measurable ContinuousMap.measurable

theorem measurable_of_continuousOn_compl_singleton [T1Space α] {f : α → γ} (a : α)
    (hf : ContinuousOn f {a}ᶜ) : Measurable f :=
  measurable_of_measurable_on_compl_singleton a
    (continuousOn_iff_continuous_restrict.1 hf).measurable
#align measurable_of_continuous_on_compl_singleton measurable_of_continuousOn_compl_singleton

theorem Continuous.measurable2 [SecondCountableTopology α] [SecondCountableTopology β] {f : δ → α}
    {g : δ → β} {c : α → β → γ} (h : Continuous fun p : α × β => c p.1 p.2) (hf : Measurable f)
    (hg : Measurable g) : Measurable fun a => c (f a) (g a) :=
  h.measurable.comp (hf.prod_mk hg)
#align continuous.measurable2 Continuous.measurable2

theorem Continuous.aemeasurable2 [SecondCountableTopology α] [SecondCountableTopology β]
    {f : δ → α} {g : δ → β} {c : α → β → γ} {μ : Measure δ}
    (h : Continuous fun p : α × β => c p.1 p.2) (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (fun a => c (f a) (g a)) μ :=
  h.measurable.comp_aemeasurable (hf.prod_mk hg)
#align continuous.ae_measurable2 Continuous.aemeasurable2

instance (priority := 100) HasContinuousInv₀.measurableInv [GroupWithZero γ] [T1Space γ]
    [HasContinuousInv₀ γ] : MeasurableInv γ :=
  ⟨measurable_of_continuousOn_compl_singleton 0 continuousOn_inv₀⟩
#align has_continuous_inv₀.has_measurable_inv HasContinuousInv₀.measurableInv

@[to_additive]
instance (priority := 100) ContinuousMul.measurableMul₂ [SecondCountableTopology γ] [Mul γ]
    [ContinuousMul γ] : MeasurableMul₂ γ :=
  ⟨continuous_mul.measurable⟩
#align has_continuous_mul.has_measurable_mul₂ ContinuousMul.measurableMul₂
#align has_continuous_add.has_measurable_mul₂ ContinuousAdd.measurableMul₂

instance (priority := 100) ContinuousSub.measurableSub₂ [SecondCountableTopology γ] [Sub γ]
    [ContinuousSub γ] : MeasurableSub₂ γ :=
  ⟨continuous_sub.measurable⟩
#align has_continuous_sub.has_measurable_sub₂ ContinuousSub.measurableSub₂

instance (priority := 100) ContinuousSMul.measurableSMul₂ {M α} [TopologicalSpace M]
    [SecondCountableTopology M] [MeasurableSpace M] [OpensMeasurableSpace M] [TopologicalSpace α]
    [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α] [SMul M α] [ContinuousSMul M α] :
    MeasurableSMul₂ M α :=
  ⟨continuous_smul.measurable⟩
#align has_continuous_smul.has_measurable_smul₂ ContinuousSMul.measurableSMul₂

end

section BorelSpace

variable [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [TopologicalSpace β]
  [MeasurableSpace β] [BorelSpace β] [TopologicalSpace γ] [MeasurableSpace γ] [BorelSpace γ]
  [MeasurableSpace δ]

theorem pi_le_borel_pi {ι : Type*} {π : ι → Type*} [∀ i, TopologicalSpace (π i)]
    [∀ i, MeasurableSpace (π i)] [∀ i, BorelSpace (π i)] :
      MeasurableSpace.pi ≤ borel (∀ i, π i) := by
  have : ‹∀ i, MeasurableSpace (π i)› = fun i => borel (π i) :=
    funext fun i => BorelSpace.measurable_eq
  rw [this]
  exact iSup_le fun i => comap_le_iff_le_map.2 <| (continuous_apply i).borel_measurable
#align pi_le_borel_pi pi_le_borel_pi

theorem prod_le_borel_prod : Prod.instMeasurableSpace ≤ borel (α × β) := by
  rw [‹BorelSpace α›.measurable_eq, ‹BorelSpace β›.measurable_eq]
  refine' sup_le _ _
  · exact comap_le_iff_le_map.mpr continuous_fst.borel_measurable
  · exact comap_le_iff_le_map.mpr continuous_snd.borel_measurable
#align prod_le_borel_prod prod_le_borel_prod

instance Pi.borelSpace {ι : Type*} {π : ι → Type*} [Countable ι] [∀ i, TopologicalSpace (π i)]
    [∀ i, MeasurableSpace (π i)] [∀ i, SecondCountableTopology (π i)] [∀ i, BorelSpace (π i)] :
    BorelSpace (∀ i, π i) :=
  ⟨le_antisymm pi_le_borel_pi OpensMeasurableSpace.borel_le⟩
#align pi.borel_space Pi.borelSpace

instance Prod.borelSpace [SecondCountableTopology α] [SecondCountableTopology β] :
    BorelSpace (α × β) :=
  ⟨le_antisymm prod_le_borel_prod OpensMeasurableSpace.borel_le⟩
#align prod.borel_space Prod.borelSpace

protected theorem Embedding.measurableEmbedding {f : α → β} (h₁ : Embedding f)
    (h₂ : MeasurableSet (range f)) : MeasurableEmbedding f :=
  show MeasurableEmbedding
      (((↑) : range f → β) ∘ (Homeomorph.ofEmbedding f h₁).toMeasurableEquiv) from
    (MeasurableEmbedding.subtype_coe h₂).comp (MeasurableEquiv.measurableEmbedding _)
#align embedding.measurable_embedding Embedding.measurableEmbedding

protected theorem ClosedEmbedding.measurableEmbedding {f : α → β} (h : ClosedEmbedding f) :
    MeasurableEmbedding f :=
  h.toEmbedding.measurableEmbedding h.closed_range.measurableSet
#align closed_embedding.measurable_embedding ClosedEmbedding.measurableEmbedding

protected theorem OpenEmbedding.measurableEmbedding {f : α → β} (h : OpenEmbedding f) :
    MeasurableEmbedding f :=
  h.toEmbedding.measurableEmbedding h.open_range.measurableSet
#align open_embedding.measurable_embedding OpenEmbedding.measurableEmbedding

section LinearOrder

variable [LinearOrder α] [OrderTopology α] [SecondCountableTopology α]

theorem measurable_of_Iio {f : δ → α} (hf : ∀ x, MeasurableSet (f ⁻¹' Iio x)) : Measurable f := by
  convert measurable_generateFrom (α := δ) _
  exact BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Iio _)
  rintro _ ⟨x, rfl⟩; exact hf x
#align measurable_of_Iio measurable_of_Iio

theorem UpperSemicontinuous.measurable [TopologicalSpace δ] [OpensMeasurableSpace δ] {f : δ → α}
    (hf : UpperSemicontinuous f) : Measurable f :=
  measurable_of_Iio fun y => (hf.isOpen_preimage y).measurableSet
#align upper_semicontinuous.measurable UpperSemicontinuous.measurable

theorem measurable_of_Ioi {f : δ → α} (hf : ∀ x, MeasurableSet (f ⁻¹' Ioi x)) : Measurable f := by
  convert measurable_generateFrom (α := δ) _
  exact BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Ioi _)
  rintro _ ⟨x, rfl⟩; exact hf x
#align measurable_of_Ioi measurable_of_Ioi

theorem LowerSemicontinuous.measurable [TopologicalSpace δ] [OpensMeasurableSpace δ] {f : δ → α}
    (hf : LowerSemicontinuous f) : Measurable f :=
  measurable_of_Ioi fun y => (hf.isOpen_preimage y).measurableSet
#align lower_semicontinuous.measurable LowerSemicontinuous.measurable

theorem measurable_of_Iic {f : δ → α} (hf : ∀ x, MeasurableSet (f ⁻¹' Iic x)) : Measurable f := by
  apply measurable_of_Ioi
  simp_rw [← compl_Iic, preimage_compl, MeasurableSet.compl_iff]
  assumption
#align measurable_of_Iic measurable_of_Iic

theorem measurable_of_Ici {f : δ → α} (hf : ∀ x, MeasurableSet (f ⁻¹' Ici x)) : Measurable f := by
  apply measurable_of_Iio
  simp_rw [← compl_Ici, preimage_compl, MeasurableSet.compl_iff]
  assumption
#align measurable_of_Ici measurable_of_Ici

theorem Measurable.isLUB {ι} [Countable ι] {f : ι → δ → α} {g : δ → α} (hf : ∀ i, Measurable (f i))
    (hg : ∀ b, IsLUB { a | ∃ i, f i b = a } (g b)) : Measurable g := by
  change ∀ b, IsLUB (range fun i => f i b) (g b) at hg
  rw [‹BorelSpace α›.measurable_eq, borel_eq_generateFrom_Ioi α]
  apply measurable_generateFrom
  rintro _ ⟨a, rfl⟩
  simp_rw [Set.preimage, mem_Ioi, lt_isLUB_iff (hg _), exists_range_iff, setOf_exists]
  exact MeasurableSet.iUnion fun i => hf i (isOpen_lt' _).measurableSet
#align measurable.is_lub Measurable.isLUB

private theorem AEMeasurable.is_lub_of_nonempty {ι} (hι : Nonempty ι) {μ : Measure δ} [Countable ι]
    {f : ι → δ → α} {g : δ → α} (hf : ∀ i, AEMeasurable (f i) μ)
    (hg : ∀ᵐ b ∂μ, IsLUB { a | ∃ i, f i b = a } (g b)) : AEMeasurable g μ := by
  let p : δ → (ι → α) → Prop := fun x f' => IsLUB { a | ∃ i, f' i = a } (g x)
  let g_seq x := ite (x ∈ aeSeqSet hf p) (g x) (⟨g x⟩ : Nonempty α).some
  have hg_seq : ∀ b, IsLUB { a | ∃ i, aeSeq hf p i b = a } (g_seq b) := by
    intro b
    haveI hα : Nonempty α := Nonempty.map g ⟨b⟩
    simp only [aeSeq]
    split_ifs with h
    · have h_set_eq :
          { a : α | ∃ i : ι, (hf i).mk (f i) b = a } = { a : α | ∃ i : ι, f i b = a } := by
        ext x
        simp_rw [Set.mem_setOf_eq, aeSeq.mk_eq_fun_of_mem_aeSeqSet hf h]
      rw [h_set_eq]
      exact aeSeq.fun_prop_of_mem_aeSeqSet hf h
    · have h_singleton : { a : α | ∃ _ : ι, hα.some = a } = {hα.some} := by
        ext1 x
        exact ⟨fun hx => hx.choose_spec.symm, fun hx => ⟨hι.some, hx.symm⟩⟩
      rw [h_singleton]
      exact isLUB_singleton
  refine' ⟨g_seq, Measurable.isLUB (aeSeq.measurable hf p) hg_seq, _⟩
  exact
    (ite_ae_eq_of_measure_compl_zero g (fun x => (⟨g x⟩ : Nonempty α).some) (aeSeqSet hf p)
        (aeSeq.measure_compl_aeSeqSet_eq_zero hf hg)).symm

theorem AEMeasurable.isLUB {ι} {μ : Measure δ} [Countable ι] {f : ι → δ → α} {g : δ → α}
    (hf : ∀ i, AEMeasurable (f i) μ) (hg : ∀ᵐ b ∂μ, IsLUB { a | ∃ i, f i b = a } (g b)) :
    AEMeasurable g μ := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · exact aemeasurable_zero_measure
  by_cases hι : Nonempty ι
  · exact AEMeasurable.is_lub_of_nonempty hι hf hg
  suffices ∃ x, g =ᵐ[μ] fun _ => g x by
    exact ⟨fun _ => g this.choose, measurable_const, this.choose_spec⟩
  have h_empty : ∀ x, { a : α | ∃ i : ι, f i x = a } = ∅ := by
    intro x
    ext1 y
    rw [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false_iff]
    exact fun hi => hι (nonempty_of_exists hi)
  simp_rw [h_empty] at hg
  exact ⟨hg.exists.choose, hg.mono fun y hy => IsLUB.unique hy hg.exists.choose_spec⟩
#align ae_measurable.is_lub AEMeasurable.isLUB

theorem Measurable.isGLB {ι} [Countable ι] {f : ι → δ → α} {g : δ → α} (hf : ∀ i, Measurable (f i))
    (hg : ∀ b, IsGLB { a | ∃ i, f i b = a } (g b)) : Measurable g := by
  change ∀ b, IsGLB (range fun i => f i b) (g b) at hg
  rw [‹BorelSpace α›.measurable_eq, borel_eq_generateFrom_Iio α]
  apply measurable_generateFrom
  rintro _ ⟨a, rfl⟩
  simp_rw [Set.preimage, mem_Iio, isGLB_lt_iff (hg _), exists_range_iff, setOf_exists]
  exact MeasurableSet.iUnion fun i => hf i (isOpen_gt' _).measurableSet
#align measurable.is_glb Measurable.isGLB

theorem AEMeasurable.isGLB {ι} {μ : Measure δ} [Countable ι] {f : ι → δ → α} {g : δ → α}
    (hf : ∀ i, AEMeasurable (f i) μ) (hg : ∀ᵐ b ∂μ, IsGLB { a | ∃ i, f i b = a } (g b)) :
    AEMeasurable g μ := by
  nontriviality α
  haveI hα : Nonempty α := inferInstance
  cases' isEmpty_or_nonempty ι with hι hι
  · simp only [IsEmpty.exists_iff, setOf_false, isGLB_empty_iff] at hg
    exact aemeasurable_const' (hg.mono fun a ha => hg.mono fun b hb => (hb _).antisymm (ha _))
  let p : δ → (ι → α) → Prop := fun x f' => IsGLB { a | ∃ i, f' i = a } (g x)
  let g_seq := (aeSeqSet hf p).piecewise g fun _ => hα.some
  have hg_seq : ∀ b, IsGLB { a | ∃ i, aeSeq hf p i b = a } (g_seq b) := by
    intro b
    simp only [aeSeq, Set.piecewise]
    split_ifs with h
    · have h_set_eq : { a : α | ∃ i : ι, (hf i).mk (f i) b = a } =
        { a : α | ∃ i : ι, f i b = a } := by
        ext x
        simp_rw [Set.mem_setOf_eq, aeSeq.mk_eq_fun_of_mem_aeSeqSet hf h]
      rw [h_set_eq]
      exact aeSeq.fun_prop_of_mem_aeSeqSet hf h
    · exact IsLeast.isGLB ⟨(@exists_const (hα.some = hα.some) ι _).2 rfl, fun x ⟨i, hi⟩ => hi.le⟩
  refine' ⟨g_seq, Measurable.isGLB (aeSeq.measurable hf p) hg_seq, _⟩
  exact
    (ite_ae_eq_of_measure_compl_zero g (fun _ => hα.some) (aeSeqSet hf p)
        (aeSeq.measure_compl_aeSeqSet_eq_zero hf hg)).symm
#align ae_measurable.is_glb AEMeasurable.isGLB

protected theorem Monotone.measurable [LinearOrder β] [OrderClosedTopology β] {f : β → α}
    (hf : Monotone f) : Measurable f :=
  suffices h : ∀ x, OrdConnected (f ⁻¹' Ioi x) from measurable_of_Ioi fun x => (h x).measurableSet
  fun _ => ordConnected_def.mpr fun _a ha _ _ _c hc => lt_of_lt_of_le ha (hf hc.1)
#align monotone.measurable Monotone.measurable

theorem aemeasurable_restrict_of_monotoneOn [LinearOrder β] [OrderClosedTopology β] {μ : Measure β}
    {s : Set β} (hs : MeasurableSet s) {f : β → α} (hf : MonotoneOn f s) :
    AEMeasurable f (μ.restrict s) :=
  have : Monotone (f ∘ (↑) : s → α) := fun ⟨x, hx⟩ ⟨y, hy⟩=> fun (hxy : x ≤ y) => hf hx hy hxy
  aemeasurable_restrict_of_measurable_subtype hs this.measurable
#align ae_measurable_restrict_of_monotone_on aemeasurable_restrict_of_monotoneOn

protected theorem Antitone.measurable [LinearOrder β] [OrderClosedTopology β] {f : β → α}
    (hf : Antitone f) : Measurable f :=
  @Monotone.measurable αᵒᵈ β _ _ ‹_› _ _ _ _ _ ‹_› _ _ _ hf
#align antitone.measurable Antitone.measurable

theorem aemeasurable_restrict_of_antitoneOn [LinearOrder β] [OrderClosedTopology β] {μ : Measure β}
    {s : Set β} (hs : MeasurableSet s) {f : β → α} (hf : AntitoneOn f s) :
    AEMeasurable f (μ.restrict s) :=
  @aemeasurable_restrict_of_monotoneOn αᵒᵈ β _ _ ‹_› _ _ _ _ _ ‹_› _ _ _ _ hs _ hf
#align ae_measurable_restrict_of_antitone_on aemeasurable_restrict_of_antitoneOn

theorem measurableSet_of_mem_nhdsWithin_Ioi_aux {s : Set α} (h : ∀ x ∈ s, s ∈ 𝓝[>] x)
    (h' : ∀ x ∈ s, ∃ y, x < y) : MeasurableSet s := by
  choose! M hM using h'
  suffices H : (s \ interior s).Countable
  · have : s = interior s ∪ s \ interior s := by rw [union_diff_cancel interior_subset]
    rw [this]
    exact isOpen_interior.measurableSet.union H.measurableSet
  have A : ∀ x ∈ s, ∃ y ∈ Ioi x, Ioo x y ⊆ s := fun x hx =>
    (mem_nhdsWithin_Ioi_iff_exists_Ioo_subset' (hM x hx)).1 (h x hx)
  choose! y hy h'y using A
  have B : Set.PairwiseDisjoint (s \ interior s) fun x => Ioo x (y x) := by
    intro x hx x' hx' hxx'
    rcases lt_or_gt_of_ne hxx' with (h' | h')
    · refine disjoint_left.2 fun z hz h'z => ?_
      have : x' ∈ interior s :=
        mem_interior.2 ⟨Ioo x (y x), h'y _ hx.1, isOpen_Ioo, ⟨h', h'z.1.trans hz.2⟩⟩
      exact False.elim (hx'.2 this)
    · refine disjoint_left.2 fun z hz h'z => ?_
      have : x ∈ interior s :=
        mem_interior.2 ⟨Ioo x' (y x'), h'y _ hx'.1, isOpen_Ioo, ⟨h', hz.1.trans h'z.2⟩⟩
      exact False.elim (hx.2 this)
  exact B.countable_of_Ioo fun x hx => hy x hx.1
#align measurable_set_of_mem_nhds_within_Ioi_aux measurableSet_of_mem_nhdsWithin_Ioi_aux

/-- If a set is a right-neighborhood of all of its points, then it is measurable. -/
theorem measurableSet_of_mem_nhdsWithin_Ioi {s : Set α} (h : ∀ x ∈ s, s ∈ 𝓝[>] x) :
    MeasurableSet s := by
  by_cases H : ∃ x ∈ s, IsTop x
  · rcases H with ⟨x₀, x₀s, h₀⟩
    have : s = {x₀} ∪ s \ {x₀} := by rw [union_diff_cancel (singleton_subset_iff.2 x₀s)]
    rw [this]
    refine' (measurableSet_singleton _).union _
    have A : ∀ x ∈ s \ {x₀}, x < x₀ := fun x hx => lt_of_le_of_ne (h₀ _) (by simpa using hx.2)
    refine' measurableSet_of_mem_nhdsWithin_Ioi_aux (fun x hx => _) fun x hx => ⟨x₀, A x hx⟩
    obtain ⟨u, hu, us⟩ : ∃ (u : α), u ∈ Ioi x ∧ Ioo x u ⊆ s :=
      (mem_nhdsWithin_Ioi_iff_exists_Ioo_subset' (A x hx)).1 (h x hx.1)
    refine' (mem_nhdsWithin_Ioi_iff_exists_Ioo_subset' (A x hx)).2 ⟨u, hu, fun y hy => ⟨us hy, _⟩⟩
    exact ne_of_lt (hy.2.trans_le (h₀ _))
  · apply measurableSet_of_mem_nhdsWithin_Ioi_aux h
    simp only [IsTop] at H
    push_neg at H
    exact H
#align measurable_set_of_mem_nhds_within_Ioi measurableSet_of_mem_nhdsWithin_Ioi

end LinearOrder

lemma ciSup_neg {α : Type _} [ConditionallyCompleteLattice α] {p : Prop} {f : p → α} (hp : ¬ p) :
    ⨆ (h : p), f h = sSup (∅ : Set α) := by
  rw [iSup]
  congr
  rw [range_eq_empty_iff]
  exact { false := hp }

lemma ciInf_neg {α : Type _} [ConditionallyCompleteLattice α] {p : Prop} {f : p → α} (hp : ¬ p) :
    ⨅ (h : p), f h = sInf (∅ : Set α) :=
  @ciSup_neg αᵒᵈ _ _ _ hp

@[measurability]
theorem Measurable.iSup_Prop {α} [MeasurableSpace α] [ConditionallyCompleteLattice α]
    (p : Prop) {f : δ → α} (hf : Measurable f) : Measurable fun b => ⨆ _ : p, f b :=
  _root_.by_cases (fun h : p => by convert hf; funext; exact ciSup_pos h) fun h : ¬p => by
    convert measurable_const using 1; funext; exact ciSup_neg h
#align measurable.supr_Prop Measurable.iSup_Prop

@[measurability]
theorem Measurable.iInf_Prop {α} [MeasurableSpace α] [ConditionallyCompleteLattice α]
    (p : Prop) {f : δ → α} (hf : Measurable f) : Measurable fun b => ⨅ _ : p, f b :=
  _root_.by_cases (fun h : p => by convert hf; funext; exact ciInf_pos h) fun h : ¬p => by
    convert measurable_const using 1; funext; exact ciInf_neg h
#align measurable.infi_Prop Measurable.iInf_Prop

section CompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α] [OrderTopology α] [SecondCountableTopology α]

open Filter

@[measurability]
theorem measurable_iSup {ι} [Countable ι] {f : ι → δ → α} (hf : ∀ i, Measurable (f i)) :
    Measurable fun b => ⨆ i, f i b := by
  have A : ∀ (i : ι) (c : α), MeasurableSet {x | c < f i x} := by
    intro i c
    apply measurableSet_lt measurable_const (hf i)
  have : ∀ (c : α), MeasurableSet (⋃ i, {x | c < f i x}) := by
    intro c
    apply MeasurableSet.iUnion (fun i ↦ A i c)
  have : MeasurableSet {x | ∃ c, ∀ i, f i x ≤ c} := by
    have : ∃ (u : ℕ → α), Tendsto u atTop atTop := by
      have : IsCountablyGenerated (atTop : Filter α) := by
        exact?
      have Z := exists_seq_tendsto (atTop : Filter α)

#exit

@[measurability]
theorem aemeasurable_iSup {ι} {μ : Measure δ} [Countable ι] {f : ι → δ → α}
    (hf : ∀ i, AEMeasurable (f i) μ) : AEMeasurable (fun b => ⨆ i, f i b) μ :=
  AEMeasurable.isLUB hf <| ae_of_all μ fun _ => isLUB_iSup
#align ae_measurable_supr aemeasurable_iSup

@[measurability]
theorem measurable_iInf {ι} [Countable ι] {f : ι → δ → α} (hf : ∀ i, Measurable (f i)) :
    Measurable fun b => ⨅ i, f i b :=
  Measurable.isGLB hf fun _ => isGLB_iInf
#align measurable_infi measurable_iInf

@[measurability]
theorem aemeasurable_iInf {ι} {μ : Measure δ} [Countable ι] {f : ι → δ → α}
    (hf : ∀ i, AEMeasurable (f i) μ) : AEMeasurable (fun b => ⨅ i, f i b) μ :=
  AEMeasurable.isGLB hf <| ae_of_all μ fun _ => isGLB_iInf
#align ae_measurable_infi aemeasurable_iInf

theorem measurable_biSup {ι} (s : Set ι) {f : ι → δ → α} (hs : s.Countable)
    (hf : ∀ i, Measurable (f i)) : Measurable fun b => ⨆ i ∈ s, f i b := by
  haveI : Encodable s := hs.toEncodable
  simp only [iSup_subtype']
  exact measurable_iSup fun i => hf i
#align measurable_bsupr measurable_biSup

theorem aemeasurable_biSup {ι} {μ : Measure δ} (s : Set ι) {f : ι → δ → α} (hs : s.Countable)
    (hf : ∀ i, AEMeasurable (f i) μ) : AEMeasurable (fun b => ⨆ i ∈ s, f i b) μ := by
  haveI : Encodable s := hs.toEncodable
  simp only [iSup_subtype']
  exact aemeasurable_iSup fun i => hf i
#align ae_measurable_bsupr aemeasurable_biSup

theorem measurable_biInf {ι} (s : Set ι) {f : ι → δ → α} (hs : s.Countable)
    (hf : ∀ i, Measurable (f i)) : Measurable fun b => ⨅ i ∈ s, f i b := by
  haveI : Encodable s := hs.toEncodable
  simp only [iInf_subtype']
  exact measurable_iInf fun i => hf i
#align measurable_binfi measurable_biInf

theorem aemeasurable_biInf {ι} {μ : Measure δ} (s : Set ι) {f : ι → δ → α} (hs : s.Countable)
    (hf : ∀ i, AEMeasurable (f i) μ) : AEMeasurable (fun b => ⨅ i ∈ s, f i b) μ := by
  haveI : Encodable s := hs.toEncodable
  simp only [iInf_subtype']
  exact aemeasurable_iInf fun i => hf i
#align ae_measurable_binfi aemeasurable_biInf

/-- `liminf` over a general filter is measurable. See `measurable_liminf` for the version over `ℕ`.
-/
theorem measurable_liminf' {ι ι'} {f : ι → δ → α} {u : Filter ι} (hf : ∀ i, Measurable (f i))
    {p : ι' → Prop} {s : ι' → Set ι} (hu : u.HasCountableBasis p s) (hs : ∀ i, (s i).Countable) :
    Measurable fun x => liminf (fun i => f i x) u := by
  simp_rw [hu.toHasBasis.liminf_eq_iSup_iInf]
  refine' measurable_biSup _ hu.countable _
  exact fun i => measurable_biInf _ (hs i) hf
#align measurable_liminf' measurable_liminf'

/-- `limsup` over a general filter is measurable. See `measurable_limsup` for the version over `ℕ`.
-/
theorem measurable_limsup' {ι ι'} {f : ι → δ → α} {u : Filter ι} (hf : ∀ i, Measurable (f i))
    {p : ι' → Prop} {s : ι' → Set ι} (hu : u.HasCountableBasis p s) (hs : ∀ i, (s i).Countable) :
    Measurable fun x => limsup (fun i => f i x) u := by
  simp_rw [hu.toHasBasis.limsup_eq_iInf_iSup]
  refine' measurable_biInf _ hu.countable _
  exact fun i => measurable_biSup _ (hs i) hf
#align measurable_limsup' measurable_limsup'

/-- `liminf` over `ℕ` is measurable. See `measurable_liminf'` for a version with a general filter.
-/
@[measurability]
theorem measurable_liminf {f : ℕ → δ → α} (hf : ∀ i, Measurable (f i)) :
    Measurable fun x => liminf (fun i => f i x) atTop :=
  measurable_liminf' hf atTop_countable_basis fun _ => to_countable _
#align measurable_liminf measurable_liminf

/-- `limsup` over `ℕ` is measurable. See `measurable_limsup'` for a version with a general filter.
-/
@[measurability]
theorem measurable_limsup {f : ℕ → δ → α} (hf : ∀ i, Measurable (f i)) :
    Measurable fun x => limsup (fun i => f i x) atTop :=
  measurable_limsup' hf atTop_countable_basis fun _ => to_countable _
#align measurable_limsup measurable_limsup

end CompleteLinearOrder

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α] [OrderTopology α] [SecondCountableTopology α]

theorem measurable_cSup {ι} {f : ι → δ → α} {s : Set ι} (hs : s.Countable)
    (hf : ∀ i, Measurable (f i)) (bdd : ∀ x, BddAbove ((fun i => f i x) '' s)) :
    Measurable fun x => sSup ((fun i => f i x) '' s) := by
  cases' eq_empty_or_nonempty s with h2s h2s
  · simp [h2s, measurable_const]
  · apply measurable_of_Iic
    intro y
    simp_rw [preimage, mem_Iic, csSup_le_iff (bdd _) (h2s.image _), ball_image_iff, setOf_forall]
    exact MeasurableSet.biInter hs fun i _ => measurableSet_le (hf i) measurable_const
#align measurable_cSup measurable_cSup

theorem measurable_cInf {ι} {f : ι → δ → α} {s : Set ι} (hs : s.Countable)
    (hf : ∀ i, Measurable (f i)) (bdd : ∀ x, BddBelow ((fun i => f i x) '' s)) :
    Measurable fun x => sInf ((fun i => f i x) '' s) :=
  @measurable_cSup αᵒᵈ _ _ _ _ _ _ _ _ _ _ _ hs hf bdd
#align measurable_cInf measurable_cInf

theorem measurable_ciSup {ι : Type*} [Countable ι] {f : ι → δ → α} (hf : ∀ i, Measurable (f i))
    (bdd : ∀ x, BddAbove (range fun i => f i x)) : Measurable fun x => ⨆ i, f i x := by
  change Measurable fun x => sSup (range fun i : ι => f i x)
  simp_rw [← image_univ] at bdd ⊢
  refine' measurable_cSup countable_univ hf bdd
#align measurable_csupr measurable_ciSup

theorem measurable_ciInf {ι : Type*} [Countable ι] {f : ι → δ → α} (hf : ∀ i, Measurable (f i))
    (bdd : ∀ x, BddBelow (range fun i => f i x)) : Measurable fun x => ⨅ i, f i x :=
  @measurable_ciSup αᵒᵈ _ _ _ _ _ _ _ _ _ _ _ hf bdd
#align measurable_cinfi measurable_ciInf

end ConditionallyCompleteLinearOrder

/-- Convert a `Homeomorph` to a `MeasurableEquiv`. -/
def Homemorph.toMeasurableEquiv (h : α ≃ₜ β) : α ≃ᵐ β where
  toEquiv := h.toEquiv
  measurable_toFun := h.continuous_toFun.measurable
  measurable_invFun := h.continuous_invFun.measurable
#align homemorph.to_measurable_equiv Homemorph.toMeasurableEquiv

protected theorem IsFiniteMeasureOnCompacts.map {α : Type*} {m0 : MeasurableSpace α}
    [TopologicalSpace α] [OpensMeasurableSpace α] {β : Type*} [MeasurableSpace β]
    [TopologicalSpace β] [BorelSpace β] [T2Space β] (μ : Measure α) [IsFiniteMeasureOnCompacts μ]
    (f : α ≃ₜ β) : IsFiniteMeasureOnCompacts (Measure.map f μ) :=
  ⟨by
    intro K hK
    rw [Measure.map_apply f.measurable hK.measurableSet]
    apply IsCompact.measure_lt_top
    rwa [f.isCompact_preimage]⟩
#align is_finite_measure_on_compacts.map IsFiniteMeasureOnCompacts.map

end BorelSpace

instance Empty.borelSpace : BorelSpace Empty :=
  ⟨borel_eq_top_of_discrete.symm⟩
#align empty.borel_space Empty.borelSpace

instance Unit.borelSpace : BorelSpace Unit :=
  ⟨borel_eq_top_of_discrete.symm⟩
#align unit.borel_space Unit.borelSpace

instance Bool.borelSpace : BorelSpace Bool :=
  ⟨borel_eq_top_of_discrete.symm⟩
#align bool.borel_space Bool.borelSpace

instance Nat.borelSpace : BorelSpace ℕ :=
  ⟨borel_eq_top_of_discrete.symm⟩
#align nat.borel_space Nat.borelSpace

instance Int.borelSpace : BorelSpace ℤ :=
  ⟨borel_eq_top_of_discrete.symm⟩
#align int.borel_space Int.borelSpace

instance Rat.borelSpace : BorelSpace ℚ :=
  ⟨borel_eq_top_of_countable.symm⟩
#align rat.borel_space Rat.borelSpace

/- Instances on `Real` and `Complex` are special cases of `IsROrC` but without these instances,
Lean fails to prove `BorelSpace (ι → ℝ)`, so we leave them here. -/
instance Real.measurableSpace : MeasurableSpace ℝ :=
  borel ℝ
#align real.measurable_space Real.measurableSpace

instance Real.borelSpace : BorelSpace ℝ :=
  ⟨rfl⟩
#align real.borel_space Real.borelSpace

instance NNReal.measurableSpace : MeasurableSpace ℝ≥0 :=
  Subtype.instMeasurableSpace
#align nnreal.measurable_space NNReal.measurableSpace

instance NNReal.borelSpace : BorelSpace ℝ≥0 :=
  Subtype.borelSpace _
#align nnreal.borel_space NNReal.borelSpace

instance ENNReal.measurableSpace : MeasurableSpace ℝ≥0∞ :=
  borel ℝ≥0∞
#align ennreal.measurable_space ENNReal.measurableSpace

instance ENNReal.borelSpace : BorelSpace ℝ≥0∞ :=
  ⟨rfl⟩
#align ennreal.borel_space ENNReal.borelSpace

instance EReal.measurableSpace : MeasurableSpace EReal :=
  borel EReal
#align ereal.measurable_space EReal.measurableSpace

instance EReal.borelSpace : BorelSpace EReal :=
  ⟨rfl⟩
#align ereal.borel_space EReal.borelSpace

/-- One can cut out `ℝ≥0∞` into the sets `{0}`, `Ico (t^n) (t^(n+1))` for `n : ℤ` and `{∞}`. This
gives a way to compute the measure of a set in terms of sets on which a given function `f` does not
fluctuate by more than `t`. -/
theorem measure_eq_measure_preimage_add_measure_tsum_Ico_zpow [MeasurableSpace α] (μ : Measure α)
    {f : α → ℝ≥0∞} (hf : Measurable f) {s : Set α} (hs : MeasurableSet s) {t : ℝ≥0} (ht : 1 < t) :
    μ s =
      μ (s ∩ f ⁻¹' {0}) + μ (s ∩ f ⁻¹' {∞}) +
      ∑' n : ℤ, μ (s ∩ f ⁻¹' Ico ((t : ℝ≥0∞) ^ n) ((t : ℝ≥0∞) ^ (n + 1))) := by
  have A : μ s = μ (s ∩ f ⁻¹' {0}) + μ (s ∩ f ⁻¹' Ioi 0) := by
    rw [← measure_union]
    · congr 1
      ext x
      have : 0 = f x ∨ 0 < f x := eq_or_lt_of_le bot_le
      rw [eq_comm] at this
      simp only [← and_or_left, this, mem_singleton_iff, mem_inter_iff, and_true_iff, mem_union,
        mem_Ioi, mem_preimage]
    · refine disjoint_left.2 fun x hx h'x => ?_
      have : 0 < f x := h'x.2
      exact lt_irrefl 0 (this.trans_le hx.2.le)
    · exact hs.inter (hf measurableSet_Ioi)
  have B : μ (s ∩ f ⁻¹' Ioi 0) = μ (s ∩ f ⁻¹' {∞}) + μ (s ∩ f ⁻¹' Ioo 0 ∞) := by
    rw [← measure_union]
    · rw [← inter_union_distrib_left]
      congr
      ext x
      simp only [mem_singleton_iff, mem_union, mem_Ioo, mem_Ioi, mem_preimage]
      have H : f x = ∞ ∨ f x < ∞ := eq_or_lt_of_le le_top
      cases' H with H H
      · simp only [H, eq_self_iff_true, or_false_iff, WithTop.zero_lt_top, not_top_lt,
          and_false_iff]
      · simp only [H, H.ne, and_true_iff, false_or_iff]
    · refine disjoint_left.2 fun x hx h'x => ?_
      have : f x < ∞ := h'x.2.2
      exact lt_irrefl _ (this.trans_le (le_of_eq hx.2.symm))
    · exact hs.inter (hf measurableSet_Ioo)
  have C : μ (s ∩ f ⁻¹' Ioo 0 ∞) =
      ∑' n : ℤ, μ (s ∩ f ⁻¹' Ico ((t : ℝ≥0∞) ^ n) ((t : ℝ≥0∞) ^ (n + 1))) := by
    rw [← measure_iUnion,
      ENNReal.Ioo_zero_top_eq_iUnion_Ico_zpow (ENNReal.one_lt_coe_iff.2 ht) ENNReal.coe_ne_top,
      preimage_iUnion, inter_iUnion]
    · intro i j
      simp only [Function.onFun]
      intro hij
      wlog h : i < j generalizing i j
      · exact (this hij.symm (hij.lt_or_lt.resolve_left h)).symm
      refine disjoint_left.2 fun x hx h'x => lt_irrefl (f x) ?_
      calc
        f x < (t : ℝ≥0∞) ^ (i + 1) := hx.2.2
        _ ≤ (t : ℝ≥0∞) ^ j := (ENNReal.zpow_le_of_le (ENNReal.one_le_coe_iff.2 ht.le) h)
        _ ≤ f x := h'x.2.1
    · intro n
      exact hs.inter (hf measurableSet_Ico)
  rw [A, B, C, add_assoc]
#align measure_eq_measure_preimage_add_measure_tsum_Ico_zpow measure_eq_measure_preimage_add_measure_tsum_Ico_zpow

section PseudoMetricSpace

variable [PseudoMetricSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]

variable [MeasurableSpace β] {x : α} {ε : ℝ}

open Metric

@[measurability]
theorem measurableSet_ball : MeasurableSet (Metric.ball x ε) :=
  Metric.isOpen_ball.measurableSet
#align measurable_set_ball measurableSet_ball

@[measurability]
theorem measurableSet_closedBall : MeasurableSet (Metric.closedBall x ε) :=
  Metric.isClosed_ball.measurableSet
#align measurable_set_closed_ball measurableSet_closedBall

@[measurability]
theorem measurable_infDist {s : Set α} : Measurable fun x => infDist x s :=
  (continuous_infDist_pt s).measurable
#align measurable_inf_dist measurable_infDist

@[measurability]
theorem Measurable.infDist {f : β → α} (hf : Measurable f) {s : Set α} :
    Measurable fun x => infDist (f x) s :=
  measurable_infDist.comp hf
#align measurable.inf_dist Measurable.infDist

@[measurability]
theorem measurable_infNndist {s : Set α} : Measurable fun x => infNndist x s :=
  (continuous_infNndist_pt s).measurable
#align measurable_inf_nndist measurable_infNndist

@[measurability]
theorem Measurable.infNndist {f : β → α} (hf : Measurable f) {s : Set α} :
    Measurable fun x => infNndist (f x) s :=
  measurable_infNndist.comp hf
#align measurable.inf_nndist Measurable.infNndist

section

variable [SecondCountableTopology α]

@[measurability]
theorem measurable_dist : Measurable fun p : α × α => dist p.1 p.2 :=
  continuous_dist.measurable
#align measurable_dist measurable_dist

@[measurability]
theorem Measurable.dist {f g : β → α} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun b => dist (f b) (g b) :=
  (@continuous_dist α _).measurable2 hf hg
#align measurable.dist Measurable.dist

@[measurability]
theorem measurable_nndist : Measurable fun p : α × α => nndist p.1 p.2 :=
  continuous_nndist.measurable
#align measurable_nndist measurable_nndist

@[measurability]
theorem Measurable.nndist {f g : β → α} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun b => nndist (f b) (g b) :=
  (@continuous_nndist α _).measurable2 hf hg
#align measurable.nndist Measurable.nndist

end

end PseudoMetricSpace

section PseudoEMetricSpace

variable [PseudoEMetricSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]

variable [MeasurableSpace β] {x : α} {ε : ℝ≥0∞}

open EMetric

@[measurability]
theorem measurableSet_eball : MeasurableSet (EMetric.ball x ε) :=
  EMetric.isOpen_ball.measurableSet
#align measurable_set_eball measurableSet_eball

@[measurability]
theorem measurable_edist_right : Measurable (edist x) :=
  (continuous_const.edist continuous_id).measurable
#align measurable_edist_right measurable_edist_right

@[measurability]
theorem measurable_edist_left : Measurable fun y => edist y x :=
  (continuous_id.edist continuous_const).measurable
#align measurable_edist_left measurable_edist_left

@[measurability]
theorem measurable_infEdist {s : Set α} : Measurable fun x => infEdist x s :=
  continuous_infEdist.measurable
#align measurable_inf_edist measurable_infEdist

@[measurability]
theorem Measurable.infEdist {f : β → α} (hf : Measurable f) {s : Set α} :
    Measurable fun x => infEdist (f x) s :=
  measurable_infEdist.comp hf
#align measurable.inf_edist Measurable.infEdist

open Metric EMetric

/-- If a set has a closed thickening with finite measure, then the measure of its `r`-closed
thickenings converges to the measure of its closure as `r` tends to `0`. -/
theorem tendsto_measure_cthickening {μ : Measure α} {s : Set α}
    (hs : ∃ R > 0, μ (cthickening R s) ≠ ∞) :
    Tendsto (fun r => μ (cthickening r s)) (𝓝 0) (𝓝 (μ (closure s))) := by
  have A : Tendsto (fun r => μ (cthickening r s)) (𝓝[Ioi 0] 0) (𝓝 (μ (closure s))) := by
    rw [closure_eq_iInter_cthickening]
    exact
      tendsto_measure_biInter_gt (fun r _ => isClosed_cthickening.measurableSet)
        (fun i j _ ij => cthickening_mono ij _) hs
  have B : Tendsto (fun r => μ (cthickening r s)) (𝓝[Iic 0] 0) (𝓝 (μ (closure s))) := by
    apply Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin (α := ℝ)] with _ hr
    rw [cthickening_of_nonpos hr]
  convert B.sup A
  exact (nhds_left_sup_nhds_right' 0).symm
#align tendsto_measure_cthickening tendsto_measure_cthickening

/-- If a closed set has a closed thickening with finite measure, then the measure of its closed
`r`-thickenings converge to its measure as `r` tends to `0`. -/
theorem tendsto_measure_cthickening_of_isClosed {μ : Measure α} {s : Set α}
    (hs : ∃ R > 0, μ (cthickening R s) ≠ ∞) (h's : IsClosed s) :
    Tendsto (fun r => μ (cthickening r s)) (𝓝 0) (𝓝 (μ s)) := by
  convert tendsto_measure_cthickening hs
  exact h's.closure_eq.symm
#align tendsto_measure_cthickening_of_is_closed tendsto_measure_cthickening_of_isClosed

/-- If a set has a thickening with finite measure, then the measures of its `r`-thickenings
converge to the measure of its closure as `r > 0` tends to `0`. -/
theorem tendsto_measure_thickening {μ : Measure α} {s : Set α}
    (hs : ∃ R > 0, μ (thickening R s) ≠ ∞) :
    Tendsto (fun r => μ (thickening r s)) (𝓝[>] 0) (𝓝 (μ (closure s))) := by
  rw [closure_eq_iInter_thickening]
  exact tendsto_measure_biInter_gt (fun r _ => isOpen_thickening.measurableSet)
      (fun i j _ ij => thickening_mono ij _) hs

/-- If a closed set has a thickening with finite measure, then the measure of its
`r`-thickenings converge to its measure as `r > 0` tends to `0`. -/
theorem tendsto_measure_thickening_of_isClosed {μ : Measure α} {s : Set α}
    (hs : ∃ R > 0, μ (thickening R s) ≠ ∞) (h's : IsClosed s) :
    Tendsto (fun r => μ (thickening r s)) (𝓝[>] 0) (𝓝 (μ s)) := by
  convert tendsto_measure_thickening hs
  exact h's.closure_eq.symm

variable [SecondCountableTopology α]

@[measurability]
theorem measurable_edist : Measurable fun p : α × α => edist p.1 p.2 :=
  continuous_edist.measurable
#align measurable_edist measurable_edist

@[measurability]
theorem Measurable.edist {f g : β → α} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun b => edist (f b) (g b) :=
  (@continuous_edist α _).measurable2 hf hg
#align measurable.edist Measurable.edist

@[measurability]
theorem AEMeasurable.edist {f g : β → α} {μ : Measure β} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) : AEMeasurable (fun a => edist (f a) (g a)) μ :=
  (@continuous_edist α _).aemeasurable2 hf hg
#align ae_measurable.edist AEMeasurable.edist

end PseudoEMetricSpace

/-- Given a compact set in a proper space, the measure of its `r`-closed thickenings converges to
its measure as `r` tends to `0`. -/
theorem tendsto_measure_cthickening_of_isCompact [MetricSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] [ProperSpace α] {μ : Measure α} [IsFiniteMeasureOnCompacts μ]
    {s : Set α} (hs : IsCompact s) :
    Tendsto (fun r => μ (Metric.cthickening r s)) (𝓝 0) (𝓝 (μ s)) :=
  tendsto_measure_cthickening_of_isClosed ⟨1, zero_lt_one, hs.bounded.cthickening.measure_lt_top.ne⟩
    hs.isClosed
#align tendsto_measure_cthickening_of_is_compact tendsto_measure_cthickening_of_isCompact

namespace Real

open MeasurableSpace MeasureTheory

theorem borel_eq_generateFrom_Ioo_rat :
    borel ℝ = .generateFrom (⋃ (a : ℚ) (b : ℚ) (_ : a < b), {Ioo (a : ℝ) (b : ℝ)}) :=
  isTopologicalBasis_Ioo_rat.borel_eq_generateFrom
#align real.borel_eq_generate_from_Ioo_rat Real.borel_eq_generateFrom_Ioo_rat

theorem isPiSystem_Ioo_rat :
    @IsPiSystem ℝ (⋃ (a : ℚ) (b : ℚ) (_ : a < b), {Ioo (a : ℝ) (b : ℝ)}) := by
  convert isPiSystem_Ioo ((↑) : ℚ → ℝ) ((↑) : ℚ → ℝ)
  ext x
  simp [eq_comm]
#align real.is_pi_system_Ioo_rat Real.isPiSystem_Ioo_rat

/-- The intervals `(-(n + 1), (n + 1))` form a finite spanning sets in the set of open intervals
with rational endpoints for a locally finite measure `μ` on `ℝ`. -/
def finiteSpanningSetsInIooRat (μ : Measure ℝ) [IsLocallyFiniteMeasure μ] :
    μ.FiniteSpanningSetsIn (⋃ (a : ℚ) (b : ℚ) (_ : a < b), {Ioo (a : ℝ) (b : ℝ)}) where
  set n := Ioo (-(n + 1)) (n + 1)
  set_mem n := by
    simp only [mem_iUnion, mem_singleton_iff]
    refine' ⟨-(n + 1 : ℕ), n + 1, _, by simp⟩
    -- TODO: norm_cast fails here?
    exact (neg_nonpos.2 (@Nat.cast_nonneg ℚ _ (n + 1))).trans_lt n.cast_add_one_pos
  finite n := measure_Ioo_lt_top
  spanning :=
    iUnion_eq_univ_iff.2 fun x =>
      ⟨⌊|x|⌋₊, neg_lt.1 ((neg_le_abs_self x).trans_lt (Nat.lt_floor_add_one _)),
        (le_abs_self x).trans_lt (Nat.lt_floor_add_one _)⟩
#align real.finite_spanning_sets_in_Ioo_rat Real.finiteSpanningSetsInIooRat

theorem measure_ext_Ioo_rat {μ ν : Measure ℝ} [IsLocallyFiniteMeasure μ]
    (h : ∀ a b : ℚ, μ (Ioo a b) = ν (Ioo a b)) : μ = ν :=
  (finiteSpanningSetsInIooRat μ).ext borel_eq_generateFrom_Ioo_rat isPiSystem_Ioo_rat <| by
    simp only [mem_iUnion, mem_singleton_iff]
    rintro _ ⟨a, b, -, rfl⟩
    apply h
#align real.measure_ext_Ioo_rat Real.measure_ext_Ioo_rat

theorem borel_eq_generateFrom_Iio_rat : borel ℝ = .generateFrom (⋃ a : ℚ, {Iio (a : ℝ)}) := by
  let g : MeasurableSpace ℝ := .generateFrom (⋃ a : ℚ, {Iio (a : ℝ)})
  refine' le_antisymm _ _
  · rw [borel_eq_generateFrom_Ioo_rat]
    refine' generateFrom_le fun t => _
    simp only [mem_iUnion, mem_singleton_iff]
    rintro ⟨a, b, _, rfl⟩
    rw [(Set.ext fun x => by
          suffices x < ↑b → (↑a < x ↔ ∃ i : ℚ, a < i ∧ ↑i ≤ x) by simpa
          refine' fun _ => ⟨fun h => _, fun ⟨i, hai, hix⟩ => (Rat.cast_lt.2 hai).trans_le hix⟩
          rcases exists_rat_btwn h with ⟨c, ac, cx⟩
          exact ⟨c, Rat.cast_lt.1 ac, cx.le⟩
            : Ioo (a : ℝ) b = (⋃ c > a, (Iio (c : ℝ))ᶜ) ∩ Iio (b : ℝ))]
    · have hg : ∀ q : ℚ, MeasurableSet[g] (Iio (q : ℝ)) := fun q =>
        GenerateMeasurable.basic (Iio (q : ℝ)) (by simp)
      refine' @MeasurableSet.inter _ g _ _ _ (hg _)
      refine' @MeasurableSet.biUnion _ _ g _ _ (to_countable _) fun c _ => _
      exact @MeasurableSet.compl _ _ g (hg _)
  · refine' MeasurableSpace.generateFrom_le fun _ => _
    simp only [mem_iUnion, mem_singleton_iff]
    rintro ⟨r, rfl⟩
    exact @measurableSet_Iio _ _ (borel ℝ) _ _ _ _
#align real.borel_eq_generate_from_Iio_rat Real.borel_eq_generateFrom_Iio_rat

end Real

variable [MeasurableSpace α]

@[measurability]
theorem measurable_real_toNNReal : Measurable Real.toNNReal :=
  continuous_real_toNNReal.measurable
#align measurable_real_to_nnreal measurable_real_toNNReal

@[measurability]
theorem Measurable.real_toNNReal {f : α → ℝ} (hf : Measurable f) :
    Measurable fun x => Real.toNNReal (f x) :=
  measurable_real_toNNReal.comp hf
#align measurable.real_to_nnreal Measurable.real_toNNReal

@[measurability]
theorem AEMeasurable.real_toNNReal {f : α → ℝ} {μ : Measure α} (hf : AEMeasurable f μ) :
    AEMeasurable (fun x => Real.toNNReal (f x)) μ :=
  measurable_real_toNNReal.comp_aemeasurable hf
#align ae_measurable.real_to_nnreal AEMeasurable.real_toNNReal

@[measurability]
theorem measurable_coe_nnreal_real : Measurable ((↑) : ℝ≥0 → ℝ) :=
  NNReal.continuous_coe.measurable
#align measurable_coe_nnreal_real measurable_coe_nnreal_real

@[measurability]
theorem Measurable.coe_nnreal_real {f : α → ℝ≥0} (hf : Measurable f) :
    Measurable fun x => (f x : ℝ) :=
  measurable_coe_nnreal_real.comp hf
#align measurable.coe_nnreal_real Measurable.coe_nnreal_real

@[measurability]
theorem AEMeasurable.coe_nnreal_real {f : α → ℝ≥0} {μ : Measure α} (hf : AEMeasurable f μ) :
    AEMeasurable (fun x => (f x : ℝ)) μ :=
  measurable_coe_nnreal_real.comp_aemeasurable hf
#align ae_measurable.coe_nnreal_real AEMeasurable.coe_nnreal_real

@[measurability]
theorem measurable_coe_nnreal_ennreal : Measurable ((↑) : ℝ≥0 → ℝ≥0∞) :=
  ENNReal.continuous_coe.measurable
#align measurable_coe_nnreal_ennreal measurable_coe_nnreal_ennreal

@[measurability]
theorem Measurable.coe_nnreal_ennreal {f : α → ℝ≥0} (hf : Measurable f) :
    Measurable fun x => (f x : ℝ≥0∞) :=
  ENNReal.continuous_coe.measurable.comp hf
#align measurable.coe_nnreal_ennreal Measurable.coe_nnreal_ennreal

@[measurability]
theorem AEMeasurable.coe_nnreal_ennreal {f : α → ℝ≥0} {μ : Measure α} (hf : AEMeasurable f μ) :
    AEMeasurable (fun x => (f x : ℝ≥0∞)) μ :=
  ENNReal.continuous_coe.measurable.comp_aemeasurable hf
#align ae_measurable.coe_nnreal_ennreal AEMeasurable.coe_nnreal_ennreal

@[measurability]
theorem Measurable.ennreal_ofReal {f : α → ℝ} (hf : Measurable f) :
    Measurable fun x => ENNReal.ofReal (f x) :=
  ENNReal.continuous_ofReal.measurable.comp hf
#align measurable.ennreal_of_real Measurable.ennreal_ofReal

@[simp, norm_cast]
theorem measurable_coe_nnreal_real_iff {f : α → ℝ≥0} :
    Measurable (fun x => f x : α → ℝ) ↔ Measurable f :=
  ⟨fun h => by simpa only [Real.toNNReal_coe] using h.real_toNNReal, Measurable.coe_nnreal_real⟩
#align measurable_coe_nnreal_real_iff measurable_coe_nnreal_real_iff

@[simp, norm_cast]
theorem aEMeasurable_coe_nnreal_real_iff {f : α → ℝ≥0} {μ : Measure α} :
    AEMeasurable (fun x => f x : α → ℝ) μ ↔ AEMeasurable f μ :=
  ⟨fun h => by simpa only [Real.toNNReal_coe] using h.real_toNNReal, AEMeasurable.coe_nnreal_real⟩
#align ae_measurable_coe_nnreal_real_iff aEMeasurable_coe_nnreal_real_iff

/-- The set of finite `ℝ≥0∞` numbers is `MeasurableEquiv` to `ℝ≥0`. -/
def MeasurableEquiv.ennrealEquivNNReal : { r : ℝ≥0∞ | r ≠ ∞ } ≃ᵐ ℝ≥0 :=
  ENNReal.neTopHomeomorphNNReal.toMeasurableEquiv
#align measurable_equiv.ennreal_equiv_nnreal MeasurableEquiv.ennrealEquivNNReal

namespace ENNReal

theorem measurable_of_measurable_nnreal {f : ℝ≥0∞ → α} (h : Measurable fun p : ℝ≥0 => f p) :
    Measurable f :=
  measurable_of_measurable_on_compl_singleton ∞
    (MeasurableEquiv.ennrealEquivNNReal.symm.measurable_comp_iff.1 h)
#align ennreal.measurable_of_measurable_nnreal ENNReal.measurable_of_measurable_nnreal

/-- `ℝ≥0∞` is `MeasurableEquiv` to `ℝ≥0 ⊕ Unit`. -/
def ennrealEquivSum : ℝ≥0∞ ≃ᵐ Sum ℝ≥0 Unit :=
  { Equiv.optionEquivSumPUnit ℝ≥0 with
    measurable_toFun := measurable_of_measurable_nnreal measurable_inl
    measurable_invFun :=
      measurable_sum measurable_coe_nnreal_ennreal (@measurable_const ℝ≥0∞ Unit _ _ ∞) }
#align ennreal.ennreal_equiv_sum ENNReal.ennrealEquivSum

open Function (uncurry)

theorem measurable_of_measurable_nnreal_prod [MeasurableSpace β] [MeasurableSpace γ]
    {f : ℝ≥0∞ × β → γ} (H₁ : Measurable fun p : ℝ≥0 × β => f (p.1, p.2))
    (H₂ : Measurable fun x => f (∞, x)) : Measurable f :=
  let e : ℝ≥0∞ × β ≃ᵐ Sum (ℝ≥0 × β) (Unit × β) :=
    (ennrealEquivSum.prodCongr (MeasurableEquiv.refl β)).trans
      (MeasurableEquiv.sumProdDistrib _ _ _)
  e.symm.measurable_comp_iff.1 <| measurable_sum H₁ (H₂.comp measurable_id.snd)
#align ennreal.measurable_of_measurable_nnreal_prod ENNReal.measurable_of_measurable_nnreal_prod

theorem measurable_of_measurable_nnreal_nnreal [MeasurableSpace β] {f : ℝ≥0∞ × ℝ≥0∞ → β}
    (h₁ : Measurable fun p : ℝ≥0 × ℝ≥0 => f (p.1, p.2)) (h₂ : Measurable fun r : ℝ≥0 => f (∞, r))
    (h₃ : Measurable fun r : ℝ≥0 => f (r, ∞)) : Measurable f :=
  measurable_of_measurable_nnreal_prod
    (measurable_swap_iff.1 <| measurable_of_measurable_nnreal_prod (h₁.comp measurable_swap) h₃)
    (measurable_of_measurable_nnreal h₂)
#align ennreal.measurable_of_measurable_nnreal_nnreal ENNReal.measurable_of_measurable_nnreal_nnreal

@[measurability]
theorem measurable_ofReal : Measurable ENNReal.ofReal :=
  ENNReal.continuous_ofReal.measurable
#align ennreal.measurable_of_real ENNReal.measurable_ofReal

@[measurability]
theorem measurable_toReal : Measurable ENNReal.toReal :=
  ENNReal.measurable_of_measurable_nnreal measurable_coe_nnreal_real
#align ennreal.measurable_to_real ENNReal.measurable_toReal

@[measurability]
theorem measurable_toNNReal : Measurable ENNReal.toNNReal :=
  ENNReal.measurable_of_measurable_nnreal measurable_id
#align ennreal.measurable_to_nnreal ENNReal.measurable_toNNReal

instance instMeasurableMul₂ : MeasurableMul₂ ℝ≥0∞ := by
  refine' ⟨measurable_of_measurable_nnreal_nnreal _ _ _⟩
  · simp only [← ENNReal.coe_mul, measurable_mul.coe_nnreal_ennreal]
  · simp only [ENNReal.top_mul', ENNReal.coe_eq_zero]
    exact measurable_const.piecewise (measurableSet_singleton _) measurable_const
  · simp only [ENNReal.mul_top', ENNReal.coe_eq_zero]
    exact measurable_const.piecewise (measurableSet_singleton _) measurable_const
#align ennreal.has_measurable_mul₂ ENNReal.instMeasurableMul₂

instance instMeasurableSub₂ : MeasurableSub₂ ℝ≥0∞ :=
  ⟨by
    apply measurable_of_measurable_nnreal_nnreal <;>
      simp [← WithTop.coe_sub]; exact continuous_sub.measurable.coe_nnreal_ennreal⟩
#align ennreal.has_measurable_sub₂ ENNReal.instMeasurableSub₂

instance instMeasurableInv : MeasurableInv ℝ≥0∞ :=
  ⟨continuous_inv.measurable⟩
#align ennreal.has_measurable_inv ENNReal.instMeasurableInv

end ENNReal

@[measurability]
theorem Measurable.ennreal_toNNReal {f : α → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun x => (f x).toNNReal :=
  ENNReal.measurable_toNNReal.comp hf
#align measurable.ennreal_to_nnreal Measurable.ennreal_toNNReal

@[measurability]
theorem AEMeasurable.ennreal_toNNReal {f : α → ℝ≥0∞} {μ : Measure α} (hf : AEMeasurable f μ) :
    AEMeasurable (fun x => (f x).toNNReal) μ :=
  ENNReal.measurable_toNNReal.comp_aemeasurable hf
#align ae_measurable.ennreal_to_nnreal AEMeasurable.ennreal_toNNReal

@[simp, norm_cast]
theorem measurable_coe_nnreal_ennreal_iff {f : α → ℝ≥0} :
    (Measurable fun x => (f x : ℝ≥0∞)) ↔ Measurable f :=
  ⟨fun h => h.ennreal_toNNReal, fun h => h.coe_nnreal_ennreal⟩
#align measurable_coe_nnreal_ennreal_iff measurable_coe_nnreal_ennreal_iff

@[simp, norm_cast]
theorem aemeasurable_coe_nnreal_ennreal_iff {f : α → ℝ≥0} {μ : Measure α} :
    AEMeasurable (fun x => (f x : ℝ≥0∞)) μ ↔ AEMeasurable f μ :=
  ⟨fun h => h.ennreal_toNNReal, fun h => h.coe_nnreal_ennreal⟩
#align ae_measurable_coe_nnreal_ennreal_iff aemeasurable_coe_nnreal_ennreal_iff

@[measurability]
theorem Measurable.ennreal_toReal {f : α → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun x => ENNReal.toReal (f x) :=
  ENNReal.measurable_toReal.comp hf
#align measurable.ennreal_to_real Measurable.ennreal_toReal

@[measurability]
theorem AEMeasurable.ennreal_toReal {f : α → ℝ≥0∞} {μ : Measure α} (hf : AEMeasurable f μ) :
    AEMeasurable (fun x => ENNReal.toReal (f x)) μ :=
  ENNReal.measurable_toReal.comp_aemeasurable hf
#align ae_measurable.ennreal_to_real AEMeasurable.ennreal_toReal

/-- note: `ℝ≥0∞` can probably be generalized in a future version of this lemma. -/
@[measurability]
theorem Measurable.ennreal_tsum {ι} [Countable ι] {f : ι → α → ℝ≥0∞} (h : ∀ i, Measurable (f i)) :
    Measurable fun x => ∑' i, f i x := by
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  apply measurable_iSup
  exact fun s => s.measurable_sum fun i _ => h i
#align measurable.ennreal_tsum Measurable.ennreal_tsum

@[measurability]
theorem Measurable.ennreal_tsum' {ι} [Countable ι] {f : ι → α → ℝ≥0∞} (h : ∀ i, Measurable (f i)) :
    Measurable (∑' i, f i) := by
  convert Measurable.ennreal_tsum h with x
  exact tsum_apply (Pi.summable.2 fun _ => ENNReal.summable)
#align measurable.ennreal_tsum' Measurable.ennreal_tsum'

@[measurability]
theorem Measurable.nnreal_tsum {ι} [Countable ι] {f : ι → α → ℝ≥0} (h : ∀ i, Measurable (f i)) :
    Measurable fun x => ∑' i, f i x := by
  simp_rw [NNReal.tsum_eq_toNNReal_tsum]
  exact (Measurable.ennreal_tsum fun i => (h i).coe_nnreal_ennreal).ennreal_toNNReal
#align measurable.nnreal_tsum Measurable.nnreal_tsum

@[measurability]
theorem AEMeasurable.ennreal_tsum {ι} [Countable ι] {f : ι → α → ℝ≥0∞} {μ : Measure α}
    (h : ∀ i, AEMeasurable (f i) μ) : AEMeasurable (fun x => ∑' i, f i x) μ := by
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  apply aemeasurable_iSup
  exact fun s => Finset.aemeasurable_sum s fun i _ => h i
#align ae_measurable.ennreal_tsum AEMeasurable.ennreal_tsum

@[measurability]
theorem AEMeasurable.nnreal_tsum {α : Type*} [MeasurableSpace α] {ι : Type*} [Countable ι]
    {f : ι → α → NNReal} {μ : MeasureTheory.Measure α} (h : ∀ i : ι, AEMeasurable (f i) μ) :
    AEMeasurable (fun x : α => ∑' i : ι, f i x) μ := by
  simp_rw [NNReal.tsum_eq_toNNReal_tsum]
  exact (AEMeasurable.ennreal_tsum fun i => (h i).coe_nnreal_ennreal).ennreal_toNNReal
#align ae_measurable.nnreal_tsum AEMeasurable.nnreal_tsum

@[measurability]
theorem measurable_coe_real_ereal : Measurable ((↑) : ℝ → EReal) :=
  continuous_coe_real_ereal.measurable
#align measurable_coe_real_ereal measurable_coe_real_ereal

@[measurability]
theorem Measurable.coe_real_ereal {f : α → ℝ} (hf : Measurable f) :
    Measurable fun x => (f x : EReal) :=
  measurable_coe_real_ereal.comp hf
#align measurable.coe_real_ereal Measurable.coe_real_ereal

@[measurability]
theorem AEMeasurable.coe_real_ereal {f : α → ℝ} {μ : Measure α} (hf : AEMeasurable f μ) :
    AEMeasurable (fun x => (f x : EReal)) μ :=
  measurable_coe_real_ereal.comp_aemeasurable hf
#align ae_measurable.coe_real_ereal AEMeasurable.coe_real_ereal

/-- The set of finite `EReal` numbers is `MeasurableEquiv` to `ℝ`. -/
def MeasurableEquiv.erealEquivReal : ({⊥, ⊤}ᶜ : Set EReal) ≃ᵐ ℝ :=
  EReal.neBotTopHomeomorphReal.toMeasurableEquiv
#align measurable_equiv.ereal_equiv_real MeasurableEquiv.erealEquivReal

theorem EReal.measurable_of_measurable_real {f : EReal → α} (h : Measurable fun p : ℝ => f p) :
    Measurable f :=
  measurable_of_measurable_on_compl_finite {⊥, ⊤} (by simp)
    (MeasurableEquiv.erealEquivReal.symm.measurable_comp_iff.1 h)
#align ereal.measurable_of_measurable_real EReal.measurable_of_measurable_real

@[measurability]
theorem measurable_ereal_toReal : Measurable EReal.toReal :=
  EReal.measurable_of_measurable_real (by simpa using measurable_id)
#align measurable_ereal_to_real measurable_ereal_toReal

@[measurability]
theorem Measurable.ereal_toReal {f : α → EReal} (hf : Measurable f) :
    Measurable fun x => (f x).toReal :=
  measurable_ereal_toReal.comp hf
#align measurable.ereal_to_real Measurable.ereal_toReal

@[measurability]
theorem AEMeasurable.ereal_toReal {f : α → EReal} {μ : Measure α} (hf : AEMeasurable f μ) :
    AEMeasurable (fun x => (f x).toReal) μ :=
  measurable_ereal_toReal.comp_aemeasurable hf
#align ae_measurable.ereal_to_real AEMeasurable.ereal_toReal

@[measurability]
theorem measurable_coe_ennreal_ereal : Measurable ((↑) : ℝ≥0∞ → EReal) :=
  continuous_coe_ennreal_ereal.measurable
#align measurable_coe_ennreal_ereal measurable_coe_ennreal_ereal

@[measurability]
theorem Measurable.coe_ereal_ennreal {f : α → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun x => (f x : EReal) :=
  measurable_coe_ennreal_ereal.comp hf
#align measurable.coe_ereal_ennreal Measurable.coe_ereal_ennreal

@[measurability]
theorem AEMeasurable.coe_ereal_ennreal {f : α → ℝ≥0∞} {μ : Measure α} (hf : AEMeasurable f μ) :
    AEMeasurable (fun x => (f x : EReal)) μ :=
  measurable_coe_ennreal_ereal.comp_aemeasurable hf
#align ae_measurable.coe_ereal_ennreal AEMeasurable.coe_ereal_ennreal

section NormedAddCommGroup

variable [NormedAddCommGroup α] [OpensMeasurableSpace α] [MeasurableSpace β]

@[measurability]
theorem measurable_norm : Measurable (norm : α → ℝ) :=
  continuous_norm.measurable
#align measurable_norm measurable_norm

@[measurability]
theorem Measurable.norm {f : β → α} (hf : Measurable f) : Measurable fun a => norm (f a) :=
  measurable_norm.comp hf
#align measurable.norm Measurable.norm

@[measurability]
theorem AEMeasurable.norm {f : β → α} {μ : Measure β} (hf : AEMeasurable f μ) :
    AEMeasurable (fun a => norm (f a)) μ :=
  measurable_norm.comp_aemeasurable hf
#align ae_measurable.norm AEMeasurable.norm

@[measurability]
theorem measurable_nnnorm : Measurable (nnnorm : α → ℝ≥0) :=
  continuous_nnnorm.measurable
#align measurable_nnnorm measurable_nnnorm

@[measurability]
theorem Measurable.nnnorm {f : β → α} (hf : Measurable f) : Measurable fun a => ‖f a‖₊ :=
  measurable_nnnorm.comp hf
#align measurable.nnnorm Measurable.nnnorm

@[measurability]
theorem AEMeasurable.nnnorm {f : β → α} {μ : Measure β} (hf : AEMeasurable f μ) :
    AEMeasurable (fun a => ‖f a‖₊) μ :=
  measurable_nnnorm.comp_aemeasurable hf
#align ae_measurable.nnnorm AEMeasurable.nnnorm

@[measurability]
theorem measurable_ennnorm : Measurable fun x : α => (‖x‖₊ : ℝ≥0∞) :=
  measurable_nnnorm.coe_nnreal_ennreal
#align measurable_ennnorm measurable_ennnorm

@[measurability]
theorem Measurable.ennnorm {f : β → α} (hf : Measurable f) : Measurable fun a => (‖f a‖₊ : ℝ≥0∞) :=
  hf.nnnorm.coe_nnreal_ennreal
#align measurable.ennnorm Measurable.ennnorm

@[measurability]
theorem AEMeasurable.ennnorm {f : β → α} {μ : Measure β} (hf : AEMeasurable f μ) :
    AEMeasurable (fun a => (‖f a‖₊ : ℝ≥0∞)) μ :=
  measurable_ennnorm.comp_aemeasurable hf
#align ae_measurable.ennnorm AEMeasurable.ennnorm

end NormedAddCommGroup
