/- -----------------------------------------------------------------------
Dependent lists.
----------------------------------------------------------------------- -/

import .c1_fin

namespace qp
namespace stdaux

universe variables ℓ₁ ℓ₂

/-! #brief A dependent list.
-/
inductive dlist {A : Type ℓ₁} (B : A → Sort ℓ₂) : list A → Type (max ℓ₁ ℓ₂)
| nil : dlist []
| cons : ∀ (a : A) (b : B a) (aa : list A) (bb : dlist aa)
         , dlist (a :: aa)

/-! #brief Equality of dlists.
-/
definition dlist.eq {A : Type ℓ₁} {B : A → Sort ℓ₂}
    : ∀ {a : A} {aa : list A}
         {b₁ b₂ : B a}
         {bb₁ bb₂ : dlist B aa}
         (ωb : b₁ = b₂)
         (ωbb : bb₁ = bb₂)
       , dlist.cons a b₁ aa bb₁ = dlist.cons a b₂ aa bb₂
| a aa b .b bb .bb (eq.refl .b) (eq.refl .bb) := rfl

/-! #brief Mapping across a dependent list.
-/
definition dlist.map {A : Type ℓ₁} {B₁ B₂ : A → Sort ℓ₂} (f : ∀ {a : A}, B₁ a → B₂ a)
    : ∀ {aa : list A}
      , dlist B₁ aa → dlist B₂ aa
| [] bb := dlist.nil B₂
| (a :: aa) (dlist.cons .a b .aa bb) := dlist.cons a (f b) aa (dlist.map bb)

/-! #brief Getting an item out of a dependent list.
-/
definition dlist.get {A : Type ℓ₁} {B : A → Sort ℓ₂}
    : ∀ {aa : list A}
        (bb : dlist B aa)
        (n : fin (list.length aa))
      , B (list.get aa n)
| [] bb n := fin.zero_elim n
| (a :: aa) (dlist.cons .a b .aa bb) (fin.mk 0 ω) := b
| (a :: aa) (dlist.cons .a b .aa bb) (fin.mk (nat.succ n) ω)
:= dlist.get bb { val := n, is_lt := nat.lt_of_succ_lt_succ ω }

theorem dlist.get.simp {A : Type ℓ₁} {B : A → Sort ℓ₂}
    (a : A) (b : B a) (aa : list A) (bb : dlist B aa)
    (n : ℕ) (ω : nat.succ n < list.length (a :: aa))
    : dlist.get (dlist.cons a b aa bb) { val := nat.succ n, is_lt := ω }
       == dlist.get bb { val := n, is_lt := nat.lt_of_succ_lt_succ ω }
:= heq.refl _

/-! #brief Getting an item out of a map.
-/
theorem dlist.get_map {A : Type ℓ₁} {B₁ B₂ : A → Sort ℓ₂} (f : ∀ {a : A}, B₁ a → B₂ a)
    : ∀ {aa : list A} (bb : dlist B₁ aa)
        (n : fin (list.length aa))
      , dlist.get (dlist.map @f bb) n = f (dlist.get bb n)
| [] bb n := fin.zero_elim n
| (a :: aa) (dlist.cons .a b .aa bb) (fin.mk 0 ω) := rfl
| (a :: aa) (dlist.cons .a b .aa bb) (fin.mk (nat.succ n) ω)
:= begin
     dsimp [dlist.map],
     apply eq_of_heq,
     apply heq.trans (dlist.get.simp a (f b) aa (dlist.map @f bb) n ω),
     apply heq_of_eq,
     apply dlist.get_map
   end

/-! #brief Dropping the bottom out of a finite function.
-/
definition fin.drop {A : Type ℓ₁} {B : A → Sort ℓ₂}
    {a : A} {aa : list A}
    (f : ∀ (n : fin (list.length (a :: aa))), B (list.get (a :: aa) n))
    : ∀ (n : fin (list.length aa))
      , B (list.get aa n)
| (fin.mk n ω) := f { val := nat.succ n, is_lt := nat.succ_lt_succ ω }

/-! #brief Inverse of dlist.get.
-/
definition dlist.enum {A : Type ℓ₁} {B : A → Sort ℓ₂}
    : ∀ {aa : list A}
        (f : ∀ (n : fin (list.length aa)), B (list.get aa n))
      , dlist B aa
| [] f := dlist.nil B
| (a :: aa) f := dlist.cons a (f fin.zero) aa (dlist.enum (fin.drop f))

/-! #brief When an enum is equal to a map.
-/
theorem dlist.enum_eq_map {A : Type ℓ₁} {B₁ B₂ : A → Sort ℓ₂} (f : ∀ {a : A}, B₁ a → B₂ a)
    : ∀ {aa : list A} (bb : dlist B₁ aa)
        (h : ∀ (n : fin (list.length aa)), B₂ (list.get aa n))
        (ωh : ∀ (n : fin (list.length aa)), h n = f (dlist.get bb n))
      , dlist.enum h = @dlist.map A B₁ B₂ @f aa bb
| [] bb h ωh := rfl
| (a :: aa) (dlist.cons .a b .aa bb) h ωh
:= begin
     dsimp [dlist.enum, dlist.map],
     rw ωh,
     apply congr_arg,
     apply dlist.enum_eq_map,
     intro n, cases n with n ωn,
     dsimp [fin.drop],
     rw ωh,
     trivial
   end

/-! #brief Getting an item out of an enumerated dlist.
-/
theorem dlist.get_enum {A : Type ℓ₁} {B : A → Sort ℓ₂}
    : ∀ {aa : list A}
        (f : ∀ (n : fin (list.length aa)), B (list.get aa n))
        (n : fin (list.length aa))
      , dlist.get (dlist.enum f) n = f n
| [] f n := fin.zero_elim n
| (a :: aa) f (fin.mk 0 ω) := rfl
| (a :: aa) f (fin.mk (nat.succ n) ω)
:= begin
     dsimp [dlist.enum, dlist.get],
     apply eq_of_heq,
     apply heq.trans (dlist.get.simp a (f fin.zero) aa _ n ω),
     apply heq_of_eq,
     apply eq.trans (dlist.get_enum (fin.drop f) _),
     trivial
   end

end stdaux
end qp
