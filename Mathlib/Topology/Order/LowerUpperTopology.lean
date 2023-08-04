/-
Copyright (c) 2023 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Topology.Homeomorph
import Mathlib.Topology.Order.Lattice
import Mathlib.Order.Hom.CompleteLattice

#align_import topology.order.lower_topology from "leanprover-community/mathlib"@"98e83c3d541c77cdb7da20d79611a780ff8e7d90"

/-!
# Lower and Upper topology

This file introduces the lower topology on a preorder as the topology generated by the complements
of the left-closed right-infinite intervals.

For completeness we also introduce the dual upper topology, generated by the complements of the
right-closed left-infinite intervals.

## Main statements

- `LowerTopology.t0Space` - the lower topology on a partial order is T₀
- `LowerTopology.isTopologicalBasis` - the complements of the upper closures of finite
  subsets form a basis for the lower topology
- `LowerTopology.continuousInf` - the inf map is continuous with respect to the lower topology

## Implementation notes

A type synonym `WithLowerTopology` is introduced and for a preorder `α`, `WithLowerTopology α`
is made an instance of `TopologicalSpace` by the topology generated by the complements of the
closed intervals to infinity.

We define a mixin class `LowerTopology` for the class of types which are both a preorder and a
topology and where the topology is generated by the complements of the closed intervals to infinity.
It is shown that `WithLowerTopology α` is an instance of `LowerTopology`.

Similarly for the upper topology.

## Motivation

The lower topology is used with the `Scott` topology to define the Lawson topology. The restriction
of the lower topology to the spectrum of a complete lattice coincides with the hull-kernel topology.

## References

* [Gierz et al, *A Compendium of Continuous Lattices*][GierzEtAl1980]

## Tags

lower topology, upper topology, preorder
-/

open Set TopologicalSpace

section WithLowerTopology

variable (α β : Type*)

/-- Type synonym for a preorder equipped with the lower topology. -/
def WithLowerTopology := α
#align with_lower_topology WithLowerTopology

variable {α β}

namespace WithLowerTopology

/-- `toLower` is the identity function to the `WithLowerTopology` of a type.  -/
@[match_pattern]
def toLower : α ≃ WithLowerTopology α := Equiv.refl _
#align with_lower_topology.to_lower WithLowerTopology.toLower

/-- `ofLower` is the identity function from the `WithLowerTopology` of a type.  -/
@[match_pattern]
def ofLower : WithLowerTopology α ≃ α := Equiv.refl _
#align with_lower_topology.of_lower WithLowerTopology.ofLower

@[simp]
theorem to_withLowerTopology_symm_eq : (@toLower α).symm = ofLower :=
  rfl
#align with_lower_topology.to_with_lower_topology_symm_eq WithLowerTopology.to_withLowerTopology_symm_eq

@[simp]
theorem of_withLowerTopology_symm_eq : (@ofLower α).symm = toLower :=
  rfl
#align with_lower_topology.of_with_lower_topology_symm_eq WithLowerTopology.of_withLowerTopology_symm_eq

@[simp]
theorem toLower_ofLower (a : WithLowerTopology α) : toLower (ofLower a) = a :=
  rfl
#align with_lower_topology.to_lower_of_lower WithLowerTopology.toLower_ofLower

@[simp]
theorem ofLower_toLower (a : α) : ofLower (toLower a) = a :=
  rfl
#align with_lower_topology.of_lower_to_lower WithLowerTopology.ofLower_toLower

-- porting note: removed @[simp] to make linter happy
theorem toLower_inj {a b : α} : toLower a = toLower b ↔ a = b :=
  Iff.rfl
#align with_lower_topology.to_lower_inj WithLowerTopology.toLower_inj

-- porting note: removed @[simp] to make linter happy
theorem ofLower_inj {a b : WithLowerTopology α} : ofLower a = ofLower b ↔ a = b :=
  Iff.rfl
#align with_lower_topology.of_lower_inj WithLowerTopology.ofLower_inj

/-- A recursor for `WithLowerTopology`. Use as `induction x using WithLowerTopology.rec`. -/
protected def rec {β : WithLowerTopology α → Sort _} (h : ∀ a, β (toLower a)) : ∀ a, β a := fun a =>
  h (ofLower a)
#align with_lower_topology.rec WithLowerTopology.rec

instance [Nonempty α] : Nonempty (WithLowerTopology α) :=
  ‹Nonempty α›

instance [Inhabited α] : Inhabited (WithLowerTopology α) :=
  ‹Inhabited α›

variable [Preorder α]

instance : Preorder (WithLowerTopology α) :=
  ‹Preorder α›

instance : TopologicalSpace (WithLowerTopology α) :=
  generateFrom { s | ∃ a, (Ici a)ᶜ = s }

theorem isOpen_preimage_ofLower (S : Set α) :
    IsOpen (WithLowerTopology.ofLower ⁻¹' S) ↔
      (generateFrom { s : Set α | ∃ a : α, (Ici a)ᶜ = s }).IsOpen S :=
  Iff.rfl
#align with_lower_topology.is_open_preimage_of_lower WithLowerTopology.isOpen_preimage_ofLower

theorem isOpen_def (T : Set (WithLowerTopology α)) :
    IsOpen T ↔ (generateFrom { s : Set α | ∃ a : α, (Ici a)ᶜ = s }).IsOpen
    (WithLowerTopology.toLower ⁻¹' T) :=
  Iff.rfl
#align with_lower_topology.is_open_def WithLowerTopology.isOpen_def

end WithLowerTopology

end WithLowerTopology

section WithUpperTopology

variable (α β : Type*)

/-- Type synonym for a preorder equipped with the upper topology. -/
def WithUpperTopology := α

variable {α β}

namespace WithUpperTopology

/-- `toUpper` is the identity function to the `WithUpperTopology` of a type.  -/
@[match_pattern]
def toUpper : α ≃ WithUpperTopology α := Equiv.refl _

/-- `ofUpper` is the identity function from the `WithUpperTopology` of a type.  -/
@[match_pattern]
def ofUpper : WithUpperTopology α ≃ α := Equiv.refl _

@[simp]
theorem to_withUpperTopology_symm_eq {α} : (@toUpper α).symm = ofUpper :=
  rfl

@[simp]
theorem of_withUpperTopology_symm_eq : (@ofUpper α).symm = toUpper :=
  rfl

@[simp]
theorem toUpper_ofUpper (a : WithUpperTopology α) : toUpper (ofUpper a) = a :=
  rfl

@[simp]
theorem ofUpper_toUpper (a : α) : ofUpper (toUpper a) = a :=
  rfl

theorem toUpper_inj {a b : α} : toUpper a = toUpper b ↔ a = b :=
  Iff.rfl

theorem ofUpper_inj {a b : WithUpperTopology α} : ofUpper a = ofUpper b ↔ a = b :=
  Iff.rfl

/-- A recursor for `WithUpperTopology`. Use as `induction x using WithUpperTopology.rec`. -/
protected def rec {β : WithUpperTopology α → Sort _} (h : ∀ a, β (toUpper a)) : ∀ a, β a := fun a =>
  h (ofUpper a)

instance [Nonempty α] : Nonempty (WithUpperTopology α) :=
  ‹Nonempty α›

instance [Inhabited α] : Inhabited (WithUpperTopology α) :=
  ‹Inhabited α›

variable [Preorder α]

instance : Preorder (WithUpperTopology α) :=
  ‹Preorder α›

instance : TopologicalSpace (WithUpperTopology α) :=
  generateFrom { s | ∃ a, (Iic a)ᶜ = s }

theorem isOpen_preimage_ofUpper (S : Set α) :
    IsOpen (WithUpperTopology.ofUpper ⁻¹' S) ↔
      (generateFrom { s : Set α | ∃ a : α, (Iic a)ᶜ = s }).IsOpen S :=
  Iff.rfl

theorem isOpen_def (T : Set (WithUpperTopology α)) :
    IsOpen T ↔ (generateFrom { s : Set α | ∃ a : α, (Iic a)ᶜ = s }).IsOpen
    (WithUpperTopology.toUpper ⁻¹' T) :=
  Iff.rfl

end WithUpperTopology

end WithUpperTopology

/--
The lower topology is the topology generated by the complements of the left-closed right-infinite
intervals.
-/
class LowerTopology (α : Type*) [t : TopologicalSpace α] [Preorder α] : Prop where
  topology_eq_lowerTopology : t = generateFrom { s | ∃ a, (Ici a)ᶜ = s }
#align lower_topology LowerTopology

/--
The upper topology is the topology generated by the complements of the right-closed left-infinite
intervals.
-/
class UpperTopology (α : Type*) [t : TopologicalSpace α] [Preorder α] : Prop where
  topology_eq_upperTopology : t = generateFrom { s | ∃ a, (Iic a)ᶜ = s }

instance [Preorder α] : LowerTopology (WithLowerTopology α) :=
  ⟨rfl⟩

instance [Preorder α] : UpperTopology (WithUpperTopology α) :=
  ⟨rfl⟩

def toOrderDualHomeomorph [Preorder α] : WithLowerTopology α ≃ₜ WithUpperTopology αᵒᵈ where
  toFun := OrderDual.toDual
  invFun := OrderDual.ofDual
  left_inv := OrderDual.toDual_ofDual
  right_inv := OrderDual.ofDual_toDual
  continuous_toFun := continuous_coinduced_rng
  continuous_invFun := continuous_coinduced_rng

namespace LowerTopology

/-- The complements of the upper closures of finite sets are a collection of lower sets
which form a basis for the lower topology. -/
def lowerBasis (α : Type*) [Preorder α] :=
  { s : Set α | ∃ t : Set α, t.Finite ∧ (upperClosure t : Set α)ᶜ = s }
#align lower_topology.lower_basis LowerTopology.lowerBasis

section Preorder

variable (α)
variable [Preorder α] [TopologicalSpace α] [LowerTopology α] {s : Set α}

lemma topology_eq : ‹_› = generateFrom { s | ∃ a : α, (Ici a)ᶜ = s } := topology_eq_lowerTopology

variable {α}

/-- If `α` is equipped with the lower topology, then it is homeomorphic to `WithLowerTopology α`.
-/
def withLowerTopologyHomeomorph : WithLowerTopology α ≃ₜ α :=
  WithLowerTopology.ofLower.toHomeomorphOfInducing ⟨by erw [topology_eq α, induced_id]; rfl⟩
#align lower_topology.with_lower_topology_homeomorph LowerTopology.withLowerTopologyHomeomorph

theorem isOpen_iff_generate_Ici_compl : IsOpen s ↔ GenerateOpen { t | ∃ a, (Ici a)ᶜ = t } s := by
  rw [topology_eq α]; rfl
#align lower_topology.is_open_iff_generate_Ici_compl LowerTopology.isOpen_iff_generate_Ici_compl

instance instUpperTopologyDual [Preorder α] [TopologicalSpace α] [LowerTopology α] :
    UpperTopology (αᵒᵈ) where
  topology_eq_upperTopology := topology_eq_lowerTopology (α := α)

/-- Left-closed right-infinite intervals [a, ∞) are closed in the lower topology. -/
theorem isClosed_Ici (a : α) : IsClosed (Ici a) :=
  isOpen_compl_iff.1 <| isOpen_iff_generate_Ici_compl.2 <| GenerateOpen.basic _ ⟨a, rfl⟩
#align lower_topology.is_closed_Ici LowerTopology.isClosed_Ici

/-- The upper closure of a finite set is closed in the lower topology. -/
theorem isClosed_upperClosure (h : s.Finite) : IsClosed (upperClosure s : Set α) := by
  simp only [← UpperSet.iInf_Ici, UpperSet.coe_iInf]
  exact isClosed_biUnion h fun a _ => isClosed_Ici a
#align lower_topology.is_closed_upper_closure LowerTopology.isClosed_upperClosure

/-- Every set open in the lower topology is a lower set. -/
theorem isLowerSet_of_isOpen (h : IsOpen s) : IsLowerSet s := by
  -- porting note: `rw` leaves a shadowed assumption
  replace h := isOpen_iff_generate_Ici_compl.1 h
  induction h
  case basic u h' => obtain ⟨a, rfl⟩ := h'; exact (isUpperSet_Ici a).compl
  case univ => exact isLowerSet_univ
  case inter u v _ _ hu2 hv2 => exact hu2.inter hv2
  case sUnion _ _ ih => exact isLowerSet_sUnion ih
#align lower_topology.is_lower_set_of_is_open LowerTopology.isLowerSet_of_isOpen

theorem isUpperSet_of_isClosed (h : IsClosed s) : IsUpperSet s :=
  isLowerSet_compl.1 <| isLowerSet_of_isOpen h.isOpen_compl
#align lower_topology.is_upper_set_of_is_closed LowerTopology.isUpperSet_of_isClosed

/--
The closure of a singleton `{a}` in the lower topology is the left-closed right-infinite interval
[a, ∞).
-/
@[simp]
theorem closure_singleton (a : α) : closure {a} = Ici a :=
  Subset.antisymm ((closure_minimal fun _ h => h.ge) <| isClosed_Ici a) <|
    (isUpperSet_of_isClosed isClosed_closure).Ici_subset <| subset_closure rfl
#align lower_topology.closure_singleton LowerTopology.closure_singleton

protected theorem isTopologicalBasis : IsTopologicalBasis (lowerBasis α) := by
  convert isTopologicalBasis_of_subbasis (topology_eq α)
  simp_rw [lowerBasis, coe_upperClosure, compl_iUnion]
  ext s
  constructor
  · rintro ⟨F, hF, rfl⟩
    refine' ⟨(fun a => (Ici a)ᶜ) '' F, ⟨hF.image _, image_subset_iff.2 fun _ _ => ⟨_, rfl⟩⟩, _⟩
    simp only [sInter_image]
  · rintro ⟨F, ⟨hF, hs⟩, rfl⟩
    haveI := hF.to_subtype
    rw [subset_def, Subtype.forall'] at hs
    choose f hf using hs
    exact ⟨_, finite_range f, by simp_rw [biInter_range, hf, sInter_eq_iInter]⟩
#align lower_topology.is_topological_basis LowerTopology.isTopologicalBasis

/-- A function `f : β → α` with lower topology in the codomain is continuous provided that the
preimage of every interval `Set.Ici a` is a closed set.

TODO: upgrade to an `iff`. -/
lemma continuous_of_Ici [TopologicalSpace β] {f : β → α} (h : ∀ a, IsClosed (f ⁻¹' (Ici a))) :
    Continuous f := by
  obtain rfl := LowerTopology.topology_eq α
  refine continuous_generateFrom ?_
  rintro _ ⟨a, rfl⟩
  exact (h a).isOpen_compl

end Preorder

section PartialOrder

variable [PartialOrder α] [TopologicalSpace α] [LowerTopology α]

-- see Note [lower instance priority]
/-- The lower topology on a partial order is T₀. -/
instance (priority := 90) t0Space : T0Space α :=
  (t0Space_iff_inseparable α).2 fun x y h =>
    Ici_injective <| by simpa only [inseparable_iff_closure_eq, closure_singleton] using h

end PartialOrder

end LowerTopology


namespace UpperTopology

/-- The complements of the lower closures of finite sets are a collection of upper sets
which form a basis for the upper topology. -/
def upperBasis (α : Type*) [Preorder α] :=
  { s : Set α | ∃ t : Set α, t.Finite ∧ (lowerClosure t : Set α)ᶜ = s }

section Preorder

variable (α)
variable [Preorder α] [TopologicalSpace α] [UpperTopology α] {s : Set α}

lemma topology_eq : ‹_› = generateFrom { s | ∃ a : α, (Iic a)ᶜ = s } := topology_eq_upperTopology

variable {α}

/-- If `α` is equipped with the upper topology, then it is homeomorphic to `WithUpperTopology α`.
-/
def withUpperTopologyHomeomorph : WithUpperTopology α ≃ₜ α :=
  WithUpperTopology.ofUpper.toHomeomorphOfInducing ⟨by erw [topology_eq α, induced_id]; rfl⟩

theorem isOpen_iff_generate_Iic_compl : IsOpen s ↔ GenerateOpen { t | ∃ a, (Iic a)ᶜ = t } s := by
  rw [topology_eq α]; rfl

instance instLowerTopologyDual [Preorder α] [TopologicalSpace α] [UpperTopology α] :
    LowerTopology (αᵒᵈ) where
  topology_eq_lowerTopology := topology_eq_upperTopology (α := α)

/-- Left-infinite right-closed intervals (-∞,a] are closed in the upper topology. -/
theorem isClosed_Iic (a : α) : IsClosed (Iic a) :=
  isOpen_compl_iff.1 <| isOpen_iff_generate_Iic_compl.2 <| GenerateOpen.basic _ ⟨a, rfl⟩

/-- The lower closure of a finite set is closed in the upper topology. -/
theorem isClosed_lowerClosure (h : s.Finite) : IsClosed (lowerClosure s : Set α) :=
  LowerTopology.isClosed_upperClosure (α := αᵒᵈ) h

/-- Every set open in the upper topology is a upper set. -/
theorem isUpperSet_of_isOpen (h : IsOpen s) : IsUpperSet s :=
  LowerTopology.isLowerSet_of_isOpen (α := αᵒᵈ) h

theorem isLowerSet_of_isClosed (h : IsClosed s) : IsLowerSet s :=
  isUpperSet_compl.1 <| isUpperSet_of_isOpen h.isOpen_compl

/--
The closure of a singleton `{a}` in the upper topology is the left-infinite right-closed interval
(-∞,a].
-/
@[simp]
theorem closure_singleton (a : α) : closure {a} = Iic a :=
  LowerTopology.closure_singleton (α := αᵒᵈ) _

protected theorem isTopologicalBasis : IsTopologicalBasis (upperBasis α) :=
  LowerTopology.isTopologicalBasis (α := αᵒᵈ)

/-- A function `f : β → α` with upper topology in the codomain is continuous provided that the
preimage of every interval `Set.Iic a` is a closed set.

TODO: upgrade to an `iff`. -/
lemma continuous_of_Iic [TopologicalSpace β] {f : β → α} (h : ∀ a, IsClosed (f ⁻¹' (Iic a))) :
    Continuous f :=
  LowerTopology.continuous_of_Ici (α := αᵒᵈ) h

end Preorder


section PartialOrder

variable [PartialOrder α] [TopologicalSpace α] [UpperTopology α]

-- see Note [lower instance priority]
/-- The upper topology on a partial order is T₀. -/
instance (priority := 90) t0Space : T0Space α :=
  LowerTopology.t0Space (α := αᵒᵈ)

end PartialOrder

end UpperTopology

instance instLowerTopologyProd [Preorder α] [TopologicalSpace α] [LowerTopology α] [OrderBot α]
    [Preorder β] [TopologicalSpace β] [LowerTopology β] [OrderBot β] : LowerTopology (α × β) where
  topology_eq_lowerTopology := by
    refine' le_antisymm (le_generateFrom _) _
    · rintro _ ⟨x, rfl⟩
      exact ((LowerTopology.isClosed_Ici _).prod <| LowerTopology.isClosed_Ici _).isOpen_compl
    rw [(LowerTopology.isTopologicalBasis.prod LowerTopology.isTopologicalBasis).eq_generateFrom,
      le_generateFrom_iff_subset_isOpen, image2_subset_iff]
    rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    dsimp
    simp_rw [coe_upperClosure, compl_iUnion, prod_eq, preimage_iInter, preimage_compl]
    -- without `let`, `refine` tries to use the product topology and fails
    let _ : TopologicalSpace (α × β) := generateFrom { s | ∃ a, (Ici a)ᶜ = s }
    refine (isOpen_biInter hs fun a _ => ?_).inter (isOpen_biInter ht fun b _ => ?_)
    · exact GenerateOpen.basic _ ⟨(a, ⊥), by simp [Ici_prod_eq, prod_univ]⟩
    · exact GenerateOpen.basic _ ⟨(⊥, b), by simp [Ici_prod_eq, univ_prod]⟩

instance instUpperTopologyProd [Preorder α] [TopologicalSpace α] [UpperTopology α] [OrderTop α]
    [Preorder β] [TopologicalSpace β] [UpperTopology β] [OrderTop β] : UpperTopology (α × β) where
  topology_eq_upperTopology := by
    suffices : LowerTopology (α × β)ᵒᵈ
    · exact LowerTopology.topology_eq_lowerTopology (α := (α × β)ᵒᵈ)
    exact instLowerTopologyProd (α := αᵒᵈ) (β := βᵒᵈ)

section CompleteLattice_LowerTopology

variable [CompleteLattice α] [CompleteLattice β] [TopologicalSpace α] [LowerTopology α]
  [TopologicalSpace β] [LowerTopology β]

protected theorem sInfHom.continuous (f : sInfHom α β) : Continuous f := by
  refine LowerTopology.continuous_of_Ici fun b => ?_
  convert LowerTopology.isClosed_Ici (sInf <| f ⁻¹' Ici b)
  refine' Subset.antisymm (fun a => sInf_le) fun a ha => le_trans _ <|
    OrderHomClass.mono (f : α →o β) ha
  refine' LE.le.trans _ (map_sInf f _).ge
  simp
#align Inf_hom.continuous sInfHom.continuous

-- see Note [lower instance priority]
instance (priority := 90) LowerTopology.continuousInf : ContinuousInf α :=
  ⟨(infsInfHom : sInfHom (α × α) α).continuous⟩
#align lower_topology.to_has_continuous_inf LowerTopology.continuousInf

end CompleteLattice_LowerTopology

section CompleteLattice_UpperTopology

variable [CompleteLattice α] [CompleteLattice β] [TopologicalSpace α] [UpperTopology α]
  [TopologicalSpace β] [UpperTopology β]

protected theorem sSupHom.continuous (f : sSupHom α β) : Continuous f :=
  sInfHom.continuous (α := αᵒᵈ) (β := βᵒᵈ) (sSupHom.dual.toFun f)

-- see Note [lower instance priority]
instance (priority := 90) UpperTopology.continuousInf : ContinuousSup α :=
  ⟨(supsSupHom : sSupHom (α × α) α).continuous⟩

end CompleteLattice_UpperTopology

lemma UpperDual_iff_Lower [Preorder α] [TopologicalSpace α] :
    UpperTopology αᵒᵈ ↔ LowerTopology α := by
  constructor
  · apply UpperTopology.instLowerTopologyDual
  · apply LowerTopology.instUpperTopologyDual

lemma LowerDual_iff_Upper [Preorder α] [TopologicalSpace α] :
    LowerTopology αᵒᵈ ↔ UpperTopology α := by
  constructor
  · apply LowerTopology.instUpperTopologyDual
  · apply UpperTopology.instLowerTopologyDual
