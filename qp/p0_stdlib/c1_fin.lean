/- -----------------------------------------------------------------------
Facts about (fin n).
----------------------------------------------------------------------- -/

import .c0_misc

namespace qp
namespace stdaux

/-! #brief Helper for showing two fin's are heq.
-/
theorem fin.heq
    : ∀ {N₁ N₂ : ℕ}
        (ωN : N₁ = N₂)
        {n₁ : fin N₁} {n₂ : fin N₂}
        (ωn : n₁^.val = n₂^.val)
      , n₁ == n₂
| N .(N) (eq.refl .(N)) (fin.mk n ω₁) (fin.mk .(n) ω₂) (eq.refl .(n)) := heq.refl _

/-! #brief The value held within a casted fin.
-/
theorem fin.cast_val
    : ∀ {N₁ N₂ : ℕ} (ωN : N₁ = N₂)
        (n : fin N₁)
      , (cast (congr_arg fin ωN) n)^.val = n^.val
| N .(N) (eq.refl .(N)) n := rfl

/-! #brief Alternate constructor for fin.
-/
definition fin_of
    {N : ℕ} (n : ℕ)
    : fin (nat.succ (N + n))
:= { val := n
   , is_lt := by calc n   < nat.succ n       : nat.less_than_or_equal.refl _
                      ... ≤ nat.succ (N + n) : nat.succ_le_succ (nat.le_add_left n N)
   }

/-! #brief An esoteric but sometimes handy constructor.
-/
definition fin.intro_zero {N : ℕ} (ωN : ¬ 0 = N)
    : fin N
:= { val := 0
   , is_lt := begin
                cases N with N,
                { exact false.elim (ωN rfl) },
                { exact (fin_of 0)^.is_lt}
              end
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

/-! #brief Enumerate a finite function.
-/
definition {ℓ} fin.enum {A : Type ℓ}
    : ∀ {N : ℕ} (f : fin N → A)
      , list A
| 0 f := []
| (nat.succ N) f:= f (fin_of 0) :: @fin.enum N (λ n, f { val := nat.succ n^.val, is_lt := nat.succ_le_succ n^.is_lt })

/-! #brief Length of an enum.
-/
theorem {ℓ} list.length_enum {A : Type ℓ}
    : ∀ {N : ℕ} (f : fin N → A)
      , list.length (fin.enum f) = N
| 0 f := rfl
| (nat.succ N) f := congr_arg nat.succ (@list.length_enum N _)

/-! #brief Action of casting on a fin.
-/
theorem fin.cast
    : ∀ {N₁ N₂ : ℕ}
        {ω : N₁ = N₂}
        {n : fin N₁}
      , cast (congr_arg fin ω) n = { val := n^.val, is_lt := cast (by subst ω) n^.is_lt }
| N .(N) (eq.refl .(N)) n := fin.eq_of_veq rfl

/-! #brief Get the nth element out of a list.
-/
definition {ℓ} list.get {A : Type ℓ}
    : ∀ (aa : list A) (n : fin (list.length aa))
      , A
| [] n := fin.zero_elim n
| (a :: aa) (fin.mk 0 ω) := a
| (a :: aa) (fin.mk (nat.succ n) ω) := list.get aa { val := n, is_lt := nat.lt_of_succ_lt_succ ω }

/-! #brief Action of list.get on fin.enum.
-/
theorem {ℓ} list.get_enum {A : Type ℓ}
    : ∀ {N : ℕ} {f : fin N → A}
        {n : fin (list.length (fin.enum f))}
      , list.get (fin.enum f) n = f (cast (congr_arg fin (list.length_enum f)) n)
| 0 f n := fin.zero_elim n
| (nat.succ N) f (fin.mk 0 ω)
:= begin
     apply congr_arg f,
     apply eq_of_heq,
     refine heq.trans _ (heq.symm (cast_heq _ _)),
     apply fin.heq (eq.symm (list.length_enum f)),
     trivial
   end
| (nat.succ N) f (fin.mk (nat.succ n) ω)
:= begin
     apply eq.trans (@list.get_enum N _ _),
     apply congr_arg f,
     apply eq_of_heq,
     refine heq.trans _ (heq.symm (cast_heq _ _)),
     apply fin.heq (eq.symm (list.length_enum f)),
     apply congr_arg nat.succ,
     apply fin.cast_val
   end

/-! #brief Action of list.get on fin.enum.
-/
theorem {ℓ} list.get_enum' {A : Type ℓ}
    {N : ℕ} {f : fin N → A}
    : list.get (fin.enum f) == f
:= begin
     refine hfunext (congr_arg fin (list.length_enum f)) _,
     intro n,
     apply list.get_enum
   end


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

/-! #brief Action of list.get on list.repeat.
-/
theorem {ℓ} list.get_repeat {A : Type ℓ}
    {a : A}
    : ∀ {N : ℕ} {n : fin (list.length (list.repeat a N))}
      , a = list.get (list.repeat a N) n
:= sorry

end stdaux
end qp
