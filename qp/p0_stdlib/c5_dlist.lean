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

-- notation `][` := dlist.nil _
-- notation h ` :Σ: ` t  := dlist.cons _ h _ t

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

/-! #brief The head of a dlist.
-/
definition dlist.head {A : Type ℓ₁} {B : A → Sort ℓ₂}
    : ∀ {a:  A} {aa : list A}
        (bb : dlist B (a :: aa))
      , B a
| a aa (dlist.cons .a b .aa bb) := b

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

/-! #brief Dropping on get.
-/
theorem dlist.drop_get {A : Type ℓ₁} {B : A → Sort ℓ₂}
    : ∀ {a : A} {b : B a} {aa : list A} {bb : dlist B aa}
         {n : ℕ} {ω : n < list.length aa}
      , dlist.get (dlist.cons a b aa bb) (fin.mk (nat.succ n) (nat.succ_lt_succ ω)) == dlist.get bb (fin.mk n ω)
| a b [] bb n ω := fin.zero_elim (fin.mk n ω)
| a₁ b₁ (a₂ :: aa) (dlist.cons .a₂ b₂ .aa bb) 0 ω := heq.refl _
| a₁ b₁ (a₂ :: aa) (dlist.cons .a₂ b₂ .aa bb) (nat.succ n) ω
:= begin
     refine heq.trans (dlist.get.simp _ _ _ _ _ _) _,
     refine heq.trans (@dlist.drop_get _ _ _ _ n (nat.lt_of_succ_lt_succ ω)) _,
     apply heq.symm,
     apply dlist.get.simp
   end

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

/-! #brief Enumerating the dlist.get function.
-/
theorem dlist.enum_get {A : Type ℓ₁} {B : A → Sort ℓ₂}
    : ∀ {aa : list A}
        {bb : dlist B aa}
      , dlist.enum (dlist.get bb) = bb
| [] bb := begin cases bb, trivial end
| (a :: aa) (dlist.cons .a b .aa bb)
:= begin
     apply dlist.eq,
     { trivial },
     { refine eq.trans _ dlist.enum_get,
       apply congr_arg dlist.enum,
       apply funext,
       intro n, cases n with n ωn,
       unfold fin.drop,
       apply eq_of_heq,
       apply dlist.drop_get
     }
   end

/-! #brief dlist.get is injective.
-/
theorem dlist.get.inj {A : Type ℓ₁} {B : A → Sort ℓ₂}
    {aa : list A}
    {bb₁ bb₂ : dlist B aa}
    (ω : dlist.get bb₁ = dlist.get bb₂)
    : bb₁ = bb₂
:= by calc bb₁ = dlist.enum (dlist.get bb₁) : eq.symm dlist.enum_get
           ... = dlist.enum (dlist.get bb₂) : by rw ω
           ... = bb₂                        : dlist.enum_get


/-! #brief Appending dlists.
-/
definition dlist.append {A : Type ℓ₁} {B : A → Sort ℓ₂}
    : ∀ {aa₁ : list A} (bb₁ : dlist B aa₁)
        {aa₂ : list A} (bb₂ : dlist B aa₂)
      , dlist B (aa₁ ++ aa₂)
| [] bb₁ aa₂ bb₂ := bb₂
| (a :: aa₁) (dlist.cons .a b .aa₁ bb₁) aa₂ bb₂ := dlist.cons a b (aa₁ ++ aa₂) (dlist.append bb₁ bb₂)

/-! #brief Splitting apart a dlist at an append (left part).
-/
definition dlist.split_left {A : Type ℓ₁} {B : A → Sort ℓ₂}
    : ∀ (aa₁ : list A) {aa₂ : list A}
        (bb : dlist B (aa₁ ++ aa₂))
      , dlist B aa₁
:= λ aa₁ aa₂ bb
   , begin
       induction aa₁ with a aa₁ rec,
       { exact dlist.nil B },
       { cases bb with a b aa₁ bb', apply dlist.cons _ b _, exact rec bb' }
     end

/-! #brief Splitting apart a dlist at an append (right part).
-/
definition dlist.split_right {A : Type ℓ₁} {B : A → Sort ℓ₂}
    : ∀ (aa₁ : list A) {aa₂ : list A}
        (bb : dlist B (aa₁ ++ aa₂))
      , dlist B aa₂
:= λ aa₁ aa₂ bb
   , begin
       induction aa₁ with a aa₁ rec,
       { exact bb },
       { cases bb with a b aa₁ bb', exact rec bb'}
     end

/-! #brief Appending the splits.
-/
theorem dlist.append_split {A : Type ℓ₁} {B : A → Sort ℓ₂}
    : ∀ {aa₁ aa₂ : list A}
        {bb : dlist B (aa₁ ++ aa₂)}
      , dlist.append (dlist.split_left _ bb) (dlist.split_right _ bb)
         = bb
:= λ aa₁ aa₂ bb
   , begin
       induction aa₁ with a aa₁ rec,
       { trivial },
       { cases bb with a b aa₁ bb',
         apply dlist.eq,
         { trivial },
         { apply rec }
       }
     end

/-! #brief Equality of appended dlists.
-/
theorem dlist.append_eq {A : Type ℓ₁} {B : A → Sort ℓ₂}
    {aa₁ aa₂ : list A}
    {bb₁ bb₂ : dlist B (aa₁ ++ aa₂)}
    (ωleft : dlist.split_left _ bb₁ = dlist.split_left _ bb₂)
    (ωright : dlist.split_right _ bb₁ = dlist.split_right _ bb₂)
    : bb₁ = bb₂
:= begin
     refine eq.trans (eq.symm dlist.append_split) _,
     refine eq.trans _ (dlist.append_split),
     rw [ωleft, ωright]
   end

/-! #brief Splitting an append.
-/
theorem dlist.split_left_append {A : Type ℓ₁} {B : A → Sort ℓ₂}
    : ∀ {aa₁ aa₂ : list A}
        {bb₁ : dlist B aa₁} {bb₂ : dlist B aa₂}
      , dlist.split_left aa₁ (dlist.append bb₁ bb₂)
         = bb₁
| aa₁ aa₂ bb₁ bb₂
:= begin
     induction aa₁ with a aa₁ rec,
     { cases bb₁ with a b aa₁ bb₁, trivial },
     { cases bb₁ with a b aa₁ bb₁,
       apply dlist.eq,
       { trivial },
       { apply rec }
     }
   end

/-! #brief Splitting an append.
-/
theorem dlist.split_right_append {A : Type ℓ₁} {B : A → Sort ℓ₂}
    : ∀ {aa₁ aa₂ : list A}
        {bb₁ : dlist B aa₁} {bb₂ : dlist B aa₂}
      , dlist.split_right aa₁ (dlist.append bb₁ bb₂)
         = bb₂
| aa₁ aa₂ bb₁ bb₂
:= begin
     induction aa₁ with a aa₁ rec,
     { cases bb₁ with a b aa₁ bb₁, trivial },
     { cases bb₁ with a b aa₁ bb₁,
       apply rec
     }
   end

/-! #brief Splitting a map.
-/
theorem dlist.split_left_map {A : Type ℓ₁} {B₁ B₂ : A → Sort ℓ₂} (f : ∀ {a : A}, B₁ a → B₂ a)
    : ∀ {aa₁ aa₂ : list A}
        {bb : dlist B₁ (aa₁ ++ aa₂)}
      , dlist.split_left aa₁ (dlist.map @f bb) = dlist.map @f (dlist.split_left aa₁ bb)
| aa₁ aa₂ bb
:= begin
     induction aa₁ with a aa₁ rec,
     { trivial },
     { cases bb with a b aa₁ bb',
       apply dlist.eq,
       { trivial },
       { apply rec }
     }
   end

/-! #brief Splitting a map.
-/
theorem dlist.split_right_map {A : Type ℓ₁} {B₁ B₂ : A → Sort ℓ₂} (f : ∀ {a : A}, B₁ a → B₂ a)
    : ∀ {aa₁ aa₂ : list A}
        {bb : dlist B₁ (aa₁ ++ aa₂)}
      , dlist.split_right aa₁ (dlist.map @f bb) = dlist.map @f (dlist.split_right aa₁ bb)
| aa₁ aa₂ bb
:= begin
     induction aa₁ with a aa₁ rec,
     { trivial },
     { cases bb with a b aa₁ bb',
       apply rec
     }
   end

/-! #brief Getting out of an append.
-/
theorem dlist.get_append {A : Type ℓ₁} {B : A → Sort ℓ₂}
    : ∀ {aa₁ aa₂ : list A}
        {bb₁ : dlist B aa₁} {bb₂ : dlist B aa₂}
        {n : ℕ} {ωn : n < list.length aa₁}
      , dlist.get (dlist.append bb₁ bb₂) (fin.mk n (list.length.grow_left ωn))
         == dlist.get bb₁ (fin.mk n ωn)
| aa₁ aa₂ bb₁ bb₂ n ωn
:= sorry

/-! #brief Getting out of a split.
-/
theorem dlist.get_split_left {A : Type ℓ₁} {B : A → Sort ℓ₂}
    : ∀ {aa₁ aa₂ : list A}
        {bb : dlist B (aa₁ ++ aa₂)}
        {n : ℕ} {ωn : n < list.length aa₁}
      , dlist.get (dlist.split_left aa₁ bb) (fin.mk n ωn)
         == dlist.get bb (fin.mk n (list.length.grow_left ωn))
:= λ aa₁ aa₂ bb n ωn
   , sorry

/-! #brief Getting out of a split.
-/
theorem dlist.get_split_right {A : Type ℓ₁} {B : A → Sort ℓ₂}
    : ∀ {aa₁ aa₂ : list A}
        {bb : dlist B (aa₁ ++ aa₂)}
        {n : ℕ} {ωn : n < list.length aa₂}
      , dlist.get (dlist.split_right aa₁ bb) (fin.mk n ωn)
         == dlist.get bb (fin.mk (n + list.length aa₁) (list.length.grow_right ωn))
:= λ aa₁ aa₂ bb n ωn
   , sorry

end stdaux
end qp
