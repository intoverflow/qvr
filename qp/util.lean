/- ----------------------------------------------------------------------------
Things that should be in the Lean standard library but aren't.
---------------------------------------------------------------------------- -/



/-! #brief funext, but at any sort.
-/
definition {ℓ₁ ℓ₂} pfunext {A : Sort ℓ₁} {B : A → Sort ℓ₂}
    {f₁ f₂ : ∀ (a : A), B a}
    (ω : ∀ (a : A), f₁ a = f₂ a)
    : f₁ = f₂
:= sorry

/-! #brief Equality helper for pprod.
-/
theorem {ℓ₁ ℓ₂} pprod.eq {A : Sort ℓ₁} {B : Sort ℓ₂}
    : ∀ {xy₁ xy₂ : pprod A B}
      , xy₁^.fst = xy₂^.fst
      → xy₁^.snd = xy₂^.snd
      → xy₁ = xy₂
| (pprod.mk x y) (pprod.mk .x .y) (eq.refl .x) (eq.refl .y)
:= rfl

/-! #brief empty, but at any sort level.
-/
inductive {ℓ} pempty : Sort ℓ

/-! #brief Eliminating a pempty.
-/
@[reducible] definition {ℓ₁ ℓ₂} pempty.elim {A : Sort ℓ₂}
    : pempty.{ℓ₁} → A
| x := begin cases x end

/-! #brief punit is uniquely inhabited.
-/
theorem {ℓ} punit.uniq
    : ∀ {x : punit.{ℓ}}
      , x = punit.star
| x := begin cases x, apply rfl end 

/-! #brief bool, but at any sort level.
-/
inductive {ℓ} pbool : Type ℓ | ff | tt

/-! #brief Chooser.
-/
@[reducible] definition {ℓ} bool.pick {A : Type ℓ} : A → A → bool → A
| a₁ a₂ bool.tt := a₁
| a₁ a₂ bool.ff := a₂

/-! #brief Dependent chooser.
-/
@[reducible] definition {ℓ} bool.dpick {A₁ A₂ : Type ℓ}
    : ∀ (a₁ : A₁) (a₂ : A₂) (b : bool), bool.pick A₁ A₂ b
| a₁ a₂ bool.tt := a₁
| a₁ a₂ bool.ff := a₂




namespace function
-- An isomorphism pair.
structure {ℓ₁ ℓ₂} isomorphism {A : Type ℓ₁} {B : Type ℓ₂}
    (f : A → B) (g : B → A)
    : Prop
:= (id₁ : left_inverse f g)
   (id₂ : left_inverse g f)

/-! #brief Composition of isomorphisms.
-/
definition {ℓ₁ ℓ₂ ℓ₃} isomorphism.comp {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
    {h : B → C} {j : C → B} (hj_iso : isomorphism h j)
    {f : A → B} {g : B → A} (fg_iso : isomorphism f g)
    : isomorphism (function.comp h f) (function.comp g j)
:= { id₁ := λ c, begin dsimp, rw [fg_iso^.id₁, hj_iso^.id₁] end
   , id₂ := λ c, begin dsimp, rw [hj_iso^.id₂, fg_iso^.id₂] end
   }
end function


/-! #brief Eliminating a fin 0.
-/
@[reducible] definition {ℓ} fin.zero_elim {A : Sort ℓ}
    : fin 0 → A
| (fin.mk n ω)
:= begin apply false.cases_on, cases ω end

/-! #brief fin 1 is uniquely inhabited.
-/
theorem fin.one
    : ∀ {n : fin 1}
      , n = { val := 0, is_lt := by apply nat.less_than_or_equal.refl }
| (fin.mk 0 ω) := rfl
| (fin.mk (nat.succ n) ω) := begin cases ω, cases a end

/-! #brief Helper to define a function out of fin.
-/
@[reducible] definition {ℓ} fin.fn {A : Type ℓ}
    : ∀ (aa : list A), fin (list.length aa) → A
| [] n := fin.zero_elim n
| (a :: aa) (fin.mk 0 ω) := a
| (a :: aa) (fin.mk (nat.succ n) ω)
:= fin.fn aa { val := n, is_lt := nat.lt_of_succ_lt_succ ω }

/-! #brief Enumerate the image of a finite function.
-/
definition {ℓ} fin.enum {A : Type ℓ}
    : ∀ {N : ℕ} (f : fin N → A)
      , list A
| 0 f := []
| (nat.succ N) f
:= list.append
    (@fin.enum N (λ n, f { val := n^.val, is_lt := nat.less_than_or_equal.step n^.is_lt }))
    [ f { val := N, is_lt := nat.less_than_or_equal.refl _ } ]

/-! #brief The length of the enumeration.
-/
@[simp] theorem {ℓ} fin.length_enum {A : Type ℓ}
    : ∀ {N : ℕ} {f : fin N → A}
      , list.length (fin.enum f) = N
| 0 f := rfl
| (nat.succ N) f
:= begin
     dsimp [fin.enum, fin.enum._main],
     apply eq.trans (list.length_append _ _),
     rw fin.length_enum,
     apply rfl
   end

/-! #brief fin.fn and fin.enum are inverses.
-/
@[simp] theorem {ℓ} fin.fn_enum {A : Type ℓ}
    : ∀ {N : ℕ} {f : fin N → A}
      , fin.fn (fin.enum f) = cast (by rw fin.length_enum) f
| 0 f := begin apply funext, intro n, exact fin.zero_elim n end
| (nat.succ N) f := sorry

namespace fin
/-! #brief The N - _ permutation.
-/
definition minus_perm {N : ℕ}
    : fin N → fin N
:= λ n, { val := N - n^.val, is_lt := sorry }

/-! #brief minus_perm is a permutation.
-/
definition minus_perm.iso {N : ℕ}
    : function.isomorphism (@minus_perm N) minus_perm
:= { id₁ := λ n, sorry
   , id₂ := λ n, sorry
   }

end fin


namespace list
/-! #brief list.nth, but without the option monad.
-/
definition {ℓ} get {A : Type ℓ}
    : ∀ (aa : list A) (idx : fin (length aa))
      , A
| [] (fin.mk idx ω) := begin apply false.rec, cases ω end
| (a :: aa) (fin.mk 0 ω) := a
| (a :: aa) (fin.mk (nat.succ idx) ω) := get aa { val := idx, is_lt := nat.lt_of_succ_lt_succ ω }

/-! #brief Permute a list.
-/
definition {ℓ} perm {A : Type ℓ}
    (aa : list A)
    {perm : fin (list.length aa) → fin (list.length aa)}
    {perm_inv : fin (list.length aa) → fin (list.length aa)}
    (perm_iso : function.isomorphism perm perm_inv)
    : list A
:= fin.enum (λ n, get aa (perm n))

/-! #brief Length of a permuted list.
-/
definition {ℓ} perm.length {A : Type ℓ}
    {aa : list A}
    {perm : fin (list.length aa) → fin (list.length aa)}
    {perm_inv : fin (list.length aa) → fin (list.length aa)}
    {perm_iso : function.isomorphism perm perm_inv}
    : length (list.perm aa perm_iso) = length aa
:= sorry
end list


-- A finite type.
structure {ℓ} FinType (T : Sort ℓ) : Type ℓ
:= (card : ℕ)
   (of_n : fin card → T)
   (n_of : T → fin card)
   (n_of_n : function.left_inverse n_of of_n)
   (of_n_of : function.left_inverse of_n n_of)

-- A boxed finite type.
structure {ℓ} BxFinType : Type (ℓ + 1)
:= (T : Type ℓ)
   (is_finite : FinType T)

/-! #brief pempty is a finite type.
-/
@[reducible] definition {ℓ} pempty.FinType
    : FinType pempty.{ℓ}
:= { card := 0
   , of_n := λ n, fin.zero_elim n
   , n_of := pempty.elim
   , n_of_n := λ n, fin.zero_elim n
   , of_n_of := λ t, begin cases t end
   }

/-! #brief punit is a finite type.
-/
@[reducible] definition {ℓ} punit.FinType
    : FinType punit.{ℓ}
:= { card := 1
   , of_n := λ n, punit.star
   , n_of := λ p, { val := 0, is_lt := by apply nat.less_than_or_equal.refl }
   , n_of_n := λ n, begin cases n, apply fin.eq_of_veq, induction val, apply rfl, cases is_lt, cases a end
   , of_n_of := λ t, eq.symm punit.uniq
   }

/-! #brief pbool is a finite type.
-/
@[reducible] definition {ℓ} pbool.FinType
    : FinType pbool.{ℓ}
:= { card := 2
   , of_n := fin.fn (pbool.ff :: pbool.tt :: [])
   , n_of := λ b, begin
                    cases b,
                    { refine { val := 0, is_lt := _ },
                      apply nat.less_than_or_equal.step,
                      apply nat.less_than_or_equal.refl,
                    },
                    { refine { val := 1, is_lt := _ },
                      apply nat.less_than_or_equal.refl,
                    }
                  end
   , n_of_n := λ n, begin
                      apply fin.eq_of_veq,
                      cases n,
                      cases val, apply rfl,
                      cases a, apply rfl,
                      cases is_lt with x₁ x₂, cases x₂ with x₃ x₄, cases x₄
                    end
   , of_n_of := λ t, begin cases t, apply rfl, apply rfl end
   }

/-! #brief fin N is a finite type.
-/
@[reducible] definition fin.FinType (N : ℕ)
    : FinType (fin N)
:= { card := N
   , of_n := λ n, n
   , n_of := λ n, n
   , n_of_n := λ n, rfl
   , of_n_of := λ n, rfl
   }
