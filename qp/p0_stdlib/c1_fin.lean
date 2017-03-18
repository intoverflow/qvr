/- -----------------------------------------------------------------------
Facts about (fin n).
----------------------------------------------------------------------- -/

namespace qp
namespace stdaux

/-! #brief Alternate constructor for fin.
-/
definition fin_of
    {N : ℕ} (n : ℕ)
    : fin (nat.succ (N + n))
:= { val := n
   , is_lt := by calc n   < nat.succ n       : nat.less_than_or_equal.refl _
                      ... ≤ nat.succ (N + n) : nat.succ_le_succ (nat.le_add_left n N)
   }

/-! #brief Adding a constant to a fin.
-/
definition fin.add {N : ℕ} (n : fin N) (m : ℕ)
    : fin (N + m)
:= { val := n^.val + m
   , is_lt := nat.add_lt_add_right n^.is_lt m
   }

/-! #brief Zero is in fin (nat.succ n).
-/
definition fin.zero {n : ℕ}
    : fin (nat.succ n)
:= fin_of 0

/-! #brief One is in fin (nat.succ (nat.succ n)).
-/
definition fin.one {n : ℕ}
    : fin (nat.succ (nat.succ n))
:= fin_of 1

/-! #brief fin 0 is uninhabited.
-/
definition {ℓ} fin.zero_elim {A : Sort ℓ}
    : fin 0 → A
| (fin.mk n ω) := false.rec A begin cases ω end

/-! #brief fin 1 is uniquely inhabited.
-/
definition fin.zero_uniq
    : ∀ (n : fin 1)
      , n = fin.zero
| (fin.mk 0 ω) := rfl
| (fin.mk (nat.succ n) ω) := begin cases ω, cases a end

/-! #brief Action of casting on a fin.
-/
theorem fin.cast
    : ∀ {N₁ N₂ : ℕ}
        {ω : N₁ = N₂}
        {n : fin N₁}
      , cast (congr_arg fin ω) n = { val := n^.val, is_lt := cast (by subst ω) n^.is_lt }
| N .N (eq.refl .N) n := fin.eq_of_veq rfl

/-! #brief Get the nth element out of a list.
-/
definition {ℓ} list.get {A : Type ℓ}
    : ∀ (aa : list A) (n : fin (list.length aa))
      , A
| [] n := fin.zero_elim n
| (a :: aa) (fin.mk 0 ω) := a
| (a :: aa) (fin.mk (nat.succ n) ω) := list.get aa { val := n, is_lt := nat.lt_of_succ_lt_succ ω }

@[simp] theorem {ℓ} list.get.simp {A : Type ℓ}
    (a : A) (aa : list A)
    (n : ℕ) (ωn : nat.succ n < list.length (a :: aa))
    : list.get (a :: aa) { val := nat.succ n, is_lt := ωn }
       = list.get aa { val := n, is_lt := nat.lt_of_succ_lt_succ ωn }
:= rfl

/-! #brief A handy lemma about lengths of lists.
-/
lemma {ℓ} list.length.grow_left {A : Type ℓ}
    {aa₁ aa₂ : list A}
    {n : ℕ}
    (ωn : n < list.length aa₁)
    : n < list.length (aa₁ ++ aa₂)
:= by calc n   < list.length aa₁                   : ωn
           ... ≤ list.length aa₁ + list.length aa₂ : nat.le_add_right _ _
           ... = list.length (aa₁ ++ aa₂)          : by rw list.length_append

/-! #brief A handy lemma about lengths of lists.
-/
lemma {ℓ} list.length.grow_right {A : Type ℓ}
    {aa₁ aa₂ : list A}
    {n : ℕ}
    (ωn : n < list.length aa₂)
    : n + list.length aa₁ < list.length (aa₁ ++ aa₂)
:= by calc n + list.length aa₁
               = list.length aa₁ + n               : by rw nat.add_comm
           ... < list.length aa₁ + list.length aa₂ : nat.add_lt_add_left ωn _
           ... = list.length (aa₁ ++ aa₂)          : by rw list.length_append

/-! #brief Action of list.get on list.append.
-/
theorem {ℓ} list.get_append_left {A : Type ℓ}
    : ∀ {aa₁ aa₂ : list A}
        {n : ℕ} {ωn : n < list.length aa₁}
      , list.get (aa₁ ++ aa₂) (fin.mk n (list.length.grow_left ωn))
         = list.get aa₁ (fin.mk n ωn)
| [] aa₂ n ωn := fin.zero_elim (fin.mk n ωn)
| (a :: aa) aa₂ 0 ω0 := rfl
| (a :: aa) aa₂ (nat.succ n) ωn
:= begin
     refine eq.trans (list.get.simp _ _ _ _) _,
     refine eq.trans _ (eq.symm (list.get.simp _ _ _ _)),
     apply list.get_append_left
   end

/-! #brief Action of list.get on list.append.
-/
theorem {ℓ} list.get_append_right {A : Type ℓ}
    : ∀ {aa₁ aa₂ : list A}
        {n : ℕ} {ωn : n < list.length aa₂}
      , list.get (aa₁ ++ aa₂) (fin.mk (n + list.length aa₁) (list.length.grow_right ωn))
         = list.get aa₂ (fin.mk n ωn)
| [] aa₂ n ωn := rfl
| (a₁ :: aa₁) [] n ωn := fin.zero_elim (fin.mk n ωn)
| (a₁ :: aa₁) (a₂ :: aa₂) 0 ω0
:= begin
     refine eq.trans (list.get.simp _ _ _ _) _,
     apply list.get_append_right
   end
| (a₁ :: aa₁) (a₂ :: aa₂) (nat.succ n) ωn
:= begin
     refine eq.trans (list.get.simp _ _ _ _) _,
     refine eq.trans _ (eq.symm (list.get.simp _ _ _ _)),
     apply list.get_append_right
   end

/-! #brief Action of list.get on list.map.
-/
theorem {ℓ₁ ℓ₂} list.get_map {A : Type ℓ₁} {B : Type ℓ₂}
    {f : A → B}
    : ∀ {aa : list A}
        {n : ℕ}
        {ωn : n < list.length aa}
        (ω : list.length aa = list.length (list.map f aa))
      , f (list.get aa { val := n, is_lt := ωn })
         = list.get (list.map f aa) { val := n, is_lt := cast begin rw ω end ωn }
| [] n ωn ω := by cases ωn
| (a :: aa) 0 ω0 ω := rfl
| (a :: aa) (nat.succ n) ωn ω
:= begin
     dsimp [list.map],
     simp,
     apply list.get_map,
     apply nat.succ.inj,
     exact ω
   end

end stdaux
end qp
