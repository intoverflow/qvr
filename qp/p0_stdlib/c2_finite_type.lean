/- -----------------------------------------------------------------------
Finite types.
----------------------------------------------------------------------- -/

import .c1_fin

namespace qp
namespace stdaux

universe variable ℓ

/-! #brief A finite sort.
-/
class FinSort (A : Sort ℓ)
    : Sort (max 1 ℓ)
:= (card : ℕ)
   (to_n : A → fin card)
   (of_n : fin card → A)
   (of_n_to : function.left_inverse of_n to_n)
   (to_n_of : function.left_inverse to_n of_n)

-- /-! #brief Cardinality is non-evil.
-- -/
-- theorem FinSort.card_nonevil {A : Sort ℓ}
--     (A_FinType₁ A_FinType₂ : FinSort A)
--     : @FinSort.card A A_FinType₁ = @FinSort.card A A_FinType₂
-- := sorry

/-! #brief Finite sorts have decidable equality.
-/
instance FinSort.decidable_eq (A : Sort ℓ)
    [A_FinSort : FinSort A]
    : decidable_eq A
:= λ a₁ a₂, if ω : FinSort.to_n a₁ = FinSort.to_n a₂
            then decidable.is_true (function.injective_of_left_inverse (FinSort.of_n_to A) ω)
            else decidable.is_false (λ ω', ω (congr_arg FinSort.to_n ω'))

/-! #brief punit is a finite sort.
-/
instance punit.FinSort
    : FinSort punit.{ℓ}
:= { card := 1
   , to_n := λ u, fin.zero
   , of_n := λ n, punit.star
   , of_n_to := λ u, begin cases u, trivial end
   , to_n_of := λ n, eq.symm (fin.zero_uniq n)
   }

/-! #brief The empty sort.
-/
inductive pempty : Sort.{ℓ}

/-! #brief punit is a finite sort.
-/
instance pempty.FinSort
    : FinSort pempty.{ℓ}
:= { card := 0
   , to_n := λ u, by cases u
   , of_n := fin.zero_elim
   , of_n_to := λ u, begin cases u end
   , to_n_of := λ n, fin.zero_elim n
   }

/-! #brief Every true proposition is a finite sort.
-/
instance Prop.true_FinSort
    (P : Prop)
    (ωP : P)
    : FinSort P
:= { card := 1
   , to_n := λ ω, fin.zero
   , of_n := λ n, ωP
   , of_n_to := λ ω, begin apply proof_irrel end
   , to_n_of := λ n, begin rw fin.zero_uniq n end
   }

/-! #brief Every false proposition is a finite sort.
-/
instance Prop.false_FinSort
    (P : Prop)
    (ωP : ¬ P)
    : FinSort P
:= { card := 0
   , to_n := λ ω, begin apply false.rec, exact ωP ω end
   , of_n := λ n, fin.zero_elim n
   , of_n_to := λ ω, begin apply proof_irrel end
   , to_n_of := λ n, fin.zero_elim n
   }

/-! #brief Every decidable proposition is a finite sort.
-/
instance Prop.decidable_FinSort
    (P : Prop)
    [P_decidable : decidable P]
    : FinSort P
:= if ω : P
    then Prop.true_FinSort P ω
    else Prop.false_FinSort P ω

/-! #brief A finite type.
-/
@[class] definition FinType (A : Type ℓ)
    : Type ℓ
:= FinSort A

definition FinType.card (A : Type ℓ)
    [A_FinType : FinType A]
:= @FinSort.card A A_FinType

definition FinType.to_n {A : Type ℓ}
    [A_FinType : FinType A]
    : A → fin (FinType.card A)
:= @FinSort.to_n A A_FinType

definition FinType.of_n {A : Type ℓ}
    [A_FinType : FinType A]
    : fin (FinType.card A) → A
:= @FinSort.of_n A A_FinType

definition FinType.of_n_to {A : Type ℓ}
    [A_FinType : FinType A]
    : function.left_inverse
        (@FinType.of_n A A_FinType)
        (@FinType.to_n A A_FinType)
:= @FinSort.of_n_to A A_FinType

definition FinType.to_n_of {A : Type ℓ}
    [A_FinType : FinType A]
    : function.left_inverse
        (@FinType.to_n A A_FinType)
        (@FinType.of_n A A_FinType)
:= @FinSort.to_n_of A A_FinType

definition FinType.enum (A : Type ℓ)
    [A_FinType : FinType A]
    : list A
:= fin.enum (@FinType.of_n A A_FinType)

/-! #brief A proposition for when a type is empty.
-/
definition IsEmptyType (A : Type ℓ)
    : Prop
:= A → false

/-! #brief A handy eliminator for empty types.
-/
definition {ℓ₂} IsEmptyType.empty_elim {A : Type ℓ}
    (A_IsEmpty : IsEmptyType A)
    {B : Sort ℓ₂}
    (a : A)
    : B
:= false.rec B (A_IsEmpty a)

/-! #brief Finite types have decidable IsTypeEmpty.
-/
instance FinType.decidable.IsEmptyType (A : Type ℓ)
    [A_FinType : FinType A]
    : decidable (IsEmptyType A)
:= if ωcard : 0 = FinType.card A
    then decidable.is_true
          (λ a, fin.zero_elim (cast (by rw ωcard) (FinType.to_n a)))
    else decidable.is_false
          (λ ω, ω (FinType.of_n (fin.intro_zero ωcard)))

/-! #brief Finite types have decidable equality.
-/
instance FinType.decidable_eq (A : Type ℓ)
    [A_FinType : FinType A]
    : decidable_eq A
:= @FinSort.decidable_eq A A_FinType

/-! #brief fin n is a finite type for all N.
-/
instance fin.FinType (N : ℕ)
    : FinType (fin N)
:= { card := N
   , to_n := λ n, n
   , of_n := λ n, n
   , of_n_to := eq.refl
   , to_n_of := eq.refl
   }

end stdaux
end qp
