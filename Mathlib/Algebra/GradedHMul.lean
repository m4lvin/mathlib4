import Mathlib.Algebra.Group.Defs

universe u₁ u₂

abbrev GradedType (M : Type u₁) := M → Type u₂

variable {M : Type u₁} {G : Type u₁}

class HasGradedHMul [Add M] (X Y : GradedType M) (Z : outParam (GradedType M)) where
  γhmul' (a b c : M) (h : a + b = c) (α : X a) (β : Y b) : Z c

def HasGradedHMul.γhmul [Add M] {X Y : GradedType M} {Z : outParam (GradedType M)}
    [HasGradedHMul X Y Z] {a b : M} (α : X a) (β : Y b) {c : M} (h : a + b = c) : Z c :=
  @HasGradedHMul.γhmul' M _ X Y Z _ a b c h α β

notation a " •[" b "] " c:80 => HasGradedHMul.γhmul a c b

variable [AddMonoid M] (X Y Z : GradedType M) (XY YZ XYZ : outParam (GradedType M))
  [HasGradedHMul X Y XY] [HasGradedHMul Y Z YZ]
  [HasGradedHMul X YZ XYZ] [HasGradedHMul XY Z XYZ]

class IsAssocGradedHMul : Prop where
  γhmul_assoc : ∀ ⦃a b c : M⦄ (α : X a) (β : Y b) (γ : Z c) (ab bc abc : M)
    (hab : a + b = ab) (hbc : b + c = bc) (habc : ab + c = abc),
      (α •[hab] β) •[habc] γ =
        α •[show a + bc = abc by rw [← hbc, ← add_assoc, hab, habc]] (β •[hbc] γ)

@[simp]
lemma γhmul_assoc_of_first_degree_eq_zero
    [IsAssocGradedHMul X Y Z XY YZ XYZ]
    {b c : M} (α : X 0) (β : Y b) (γ : Z c) (bc : M) (hbc : b + c = bc) :
  (α •[zero_add _] β) •[hbc] γ = α •[zero_add _] β •[hbc] γ := by
  apply IsAssocGradedHMul.γhmul_assoc

@[simp]
lemma γhmul_assoc_of_second_degree_eq_zero
    [IsAssocGradedHMul X Y Z XY YZ XYZ]
    {a c : M} (α : X a) (β : Y 0) (γ : Z c) (ac : M) (hac : a + c = ac) :
  (α •[add_zero _] β) •[hac] γ = α •[hac] β •[zero_add _] γ := by
  apply IsAssocGradedHMul.γhmul_assoc

@[simp]
lemma γhmul_assoc_of_third_degree_eq_zero
    [IsAssocGradedHMul X Y Z XY YZ XYZ]
    {a b : M} (α : X a) (β : Y b) (γ : Z 0) (ab : M) (hab : a + b = ab) :
  (α •[hab] β) •[add_zero _] γ = α •[hab] β •[add_zero _] γ := by
  apply IsAssocGradedHMul.γhmul_assoc

variable [AddGroup G] (X' Y' Z' : GradedType G) (XY' YZ' XYZ' : outParam (GradedType G))
  [HasGradedHMul X' Y' XY'] [HasGradedHMul Y' Z' YZ']
  [HasGradedHMul X' YZ' XYZ'] [HasGradedHMul XY' Z' XYZ']

@[simp]
lemma γhmul_assoc_of_second_degree_eq_neg_third_degree
    [IsAssocGradedHMul X' Y' Z' XY' YZ' XYZ']
    {a b ab : G} (α : X' a) (β : Y' (-b)) (γ : Z' b) (hab : a + (-b) = ab) :
    (α •[hab] β) •[show ab + b = a by rw [← hab, add_assoc, neg_add_self, add_zero]] γ =
      α •[add_zero a] (β •[neg_add_self b] γ) := by
  apply IsAssocGradedHMul.γhmul_assoc