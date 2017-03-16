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
