/- -----------------------------------------------------------------------
Facts about algebraic structures.
----------------------------------------------------------------------- -/

namespace qp
namespace stdaux

universe variables ℓ₁ ℓ₂ ℓ₃

/-! #brief A semigroup homomorphism.
-/
structure semigroup.hom
    {A : Type ℓ₁} [A_semigroup : semigroup A]
    {B : Type ℓ₂} [B_semigroup : semigroup B]
    (f : A → B)
    : Prop
:= (dist : ∀ (a₁ a₂ : A), f (a₁ * a₂) = f a₁ * f a₂)

/-! #brief A commutative semigroup homomorphism.
-/
structure comm_semigroup.hom
    {A : Type ℓ₁} [A_comm_semigroup : comm_semigroup A]
    {B : Type ℓ₂} [B_comm_semigroup : comm_semigroup B]
    (f : A → B)
    extends semigroup.hom f
    : Prop

/-! #brief Semigroup homomorphisms are closed under composition.
-/
definition semigroup.hom_comp
    {A : Type ℓ₁} [A_semigroup : semigroup A]
    {B : Type ℓ₂} [B_semigroup : semigroup B]
    {C : Type ℓ₃} [C_semigroup : semigroup C]
    {g : B → C} (g_hom : semigroup.hom g)
    {f : A → B} (f_hom : semigroup.hom f)
    : semigroup.hom (function.comp g f)
:= { dist := λ a₁ a₂, by rw [-g_hom^.dist, -f_hom^.dist]
   }

/-! #brief The identity function is a semigroup homomorphism.
-/
definition semigroup.hom_id
    (A : Type ℓ₁) [A_semigroup : semigroup A]
    : semigroup.hom (@id A)
:= { dist := λ a₁ a₂, rfl }

/-! #brief A monoid homomorphism.
-/
structure monoid.hom
    {A : Type ℓ₁} [A_monoid : monoid A]
    {B : Type ℓ₂} [B_monoid : monoid B]
    (f : A → B)
    extends semigroup.hom f
    : Prop
:= (id : f 1 = 1)

/-! #brief A commutative monoid homomorphism.
-/
structure comm_monoid.hom
    {A : Type ℓ₁} [A_comm_monoid : comm_monoid A]
    {B : Type ℓ₂} [B_comm_monoid : comm_monoid B]
    (f : A → B)
    extends monoid.hom f
    : Prop

/-! #brief Monoid homomorphisms are closed under composition.
-/
definition monoid.hom_comp
    {A : Type ℓ₁} [A_monoid : monoid A]
    {B : Type ℓ₂} [B_monoid : monoid B]
    {C : Type ℓ₃} [C_monoid : monoid C]
    {g : B → C} (g_hom : monoid.hom g)
    {f : A → B} (f_hom : monoid.hom f)
    : monoid.hom (function.comp g f)
:= { dist := λ a₁ a₂, by rw [-g_hom^.dist, -f_hom^.dist]
   , id := by rw [-g_hom^.id, -f_hom^.id]
   }

/-! #brief The identity function is a monoid homomorphism.
-/
definition monoid.hom_id
    (A : Type ℓ₁) [A_monoid : monoid A]
    : monoid.hom (@id A)
:= { dist := (semigroup.hom_id A)^.dist
   , id := rfl
   }

/-! #brief A group homomorphism.
-/
structure group.hom
    {A : Type ℓ₁} [A_group : group A]
    {B : Type ℓ₂} [B_group : group B]
    (f : A → B)
    extends semigroup.hom f
    : Prop

/-! #brief A commutative group homomorphism.
-/
structure comm_group.hom
    {A : Type ℓ₁} [A_comm_group : comm_group A]
    {B : Type ℓ₂} [B_comm_group : comm_group B]
    (f : A → B)
    extends group.hom f
    : Prop

/-! #brief Group homomorphisms are closed under composition.
-/
definition group.hom_comp
    {A : Type ℓ₁} [A_group : group A]
    {B : Type ℓ₂} [B_group : group B]
    {C : Type ℓ₃} [C_group : group C]
    {g : B → C} (g_hom : group.hom g)
    {f : A → B} (f_hom : group.hom f)
    : group.hom (function.comp g f)
:= { dist := (semigroup.hom_comp (group.hom.to_hom g_hom) (group.hom.to_hom f_hom))^.dist
   }

/-! #brief The identity function is a group homomorphism.
-/
definition group.hom_id
    (A : Type ℓ₁) [A_group : group A]
    : group.hom (@id A)
:= { dist := (semigroup.hom_id A)^.dist
   }

/-! #brief Idempotents in groups are trivial.
-/
theorem group.idempotent {A : Type ℓ₁} [A_group : group A]
    {a : A}
    (ω : a = a * a)
    : a = 1
:= by calc a   = a * 1         : by rw mul_one
           ... = a * (a * a⁻¹) : by rw mul_right_inv
           ... = (a * a) * a⁻¹ : by rw mul_assoc
           ... = a * a⁻¹       : by rw -ω
           ... = 1             : by rw mul_right_inv


/-! #brief Inverses in a group are unique.
-/
theorem group.inv_uniq
    {A : Type ℓ₁} [A_group : group A]
    {a b : A}
    (ω : a * b = 1)
    : b = a⁻¹
:= by calc b   = 1 * b : by rw one_mul
           ... = (a⁻¹ * a) * b : by rw mul_left_inv
           ... = a⁻¹ * (a * b) : by rw mul_assoc
           ... = a⁻¹ * 1       : by rw ω
           ... = a⁻¹           : by rw mul_one

/-! #brief Group homomorphisms preserve identities.
-/
theorem group.hom_one
    {A : Type ℓ₁} [A_group : group A]
    {B : Type ℓ₂} [B_group : group B]
    {f : A → B}
    (f_hom : group.hom f)
    : f 1 = 1
:= group.idempotent
    (by calc f 1 = f (1 * 1) : by rw mul_one
             ... = f 1 * f 1 : by rw f_hom^.dist)

/-! #brief Group homomorphisms preserve inverses.
-/
theorem group.hom_inv
    {A : Type ℓ₁} [A_group : group A]
    {B : Type ℓ₂} [B_group : group B]
    {f : A → B}
    (f_hom : group.hom f)
    (a : A)
    : f (a⁻¹) = (f a)⁻¹
:= group.inv_uniq
    (by calc f a * f (a⁻¹)
                 = f (a * a⁻¹)   : by rw f_hom^.dist
             ... = f 1           : by rw mul_right_inv
             ... = 1             : by rw group.hom_one f_hom)

/-! #brief Every group homomorphism is a monoid homomorphism.
-/
definition group.hom.to_monoid_hom
    {A : Type ℓ₁} [A_group : group A]
    {B : Type ℓ₂} [B_group : group B]
    {f : A → B}
    (f_hom : group.hom f)
    : monoid.hom f
:= { dist := f_hom^.dist
   , id := group.hom_one f_hom
   }

/-! #brief A homomorphism of commutative rings.
-/
structure comm_ring.hom
    {A : Type ℓ₁} [A_comm_ring : comm_ring A]
    {B : Type ℓ₂} [B_comm_ring : comm_ring B]
    (f : A → B)
    : Prop
:= (add : ∀ (a₁ a₂ : A), f (a₁ + a₂) = f a₁ + f a₂)
   (mul : ∀ (a₁ a₂ : A), f (a₁ * a₂) = f a₁ * f a₂)
   (one : f 1 = 1)

/-! #brief The identity function is a commutative ring homomorphism.
-/
definition comm_ring.hom_id
    {A : Type ℓ₁} [A_comm_ring : comm_ring A]
    : comm_ring.hom (@id A)
:= { add := λ a₁ a₂, rfl
   , mul := λ a₁ a₂, rfl
   , one := rfl
   }

/-! #brief Commutative ring homomorphisms are closed under composition.
-/
definition comm_ring.hom_comp
    {A : Type ℓ₁} [A_comm_ring : comm_ring A]
    {B : Type ℓ₂} [B_comm_ring : comm_ring B]
    {C : Type ℓ₃} [C_comm_ring : comm_ring C]
    {g : B → C} (g_hom : comm_ring.hom g)
    {f : A → B} (f_hom : comm_ring.hom f)
    : comm_ring.hom (function.comp g f)
:= { add := λ a₁ a₂, by rw [-g_hom^.add, -f_hom^.add]
   , mul := λ a₁ a₂, by rw [-g_hom^.mul, -f_hom^.mul]
   , one :=  by rw [-g_hom^.one, -f_hom^.one]
   }


end stdaux
end qp
