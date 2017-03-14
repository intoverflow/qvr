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
