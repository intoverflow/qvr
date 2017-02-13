/- ----------------------------------------------------------------------------
Things that should be in the Lean standard library but aren't.
---------------------------------------------------------------------------- -/



/-! #brief empty, but at any type level.
-/
inductive {ℓ} poly_empty : Type ℓ

/-! #brief Eliminating a poly_empty.
-/
@[reducible] definition {ℓ₁ ℓ₂} poly_empty.elim {A : Type ℓ₂}
    : poly_empty.{ℓ₁} → A
| x := begin cases x end

/-! #brief poly_unit is uniquely inhabited.
-/
theorem {ℓ} poly_unit.uniq
    : ∀ {x : poly_unit.{ℓ}}
      , x = poly_unit.star
| x := begin cases x, apply rfl end 

/-! #brief bool, but at any type level.
-/
inductive {ℓ} poly_bool : Type (max 1 ℓ) | ff | tt

namespace list
/-! #brief list.nth, but without the option monad.
-/
@[reducible] definition {ℓ} get {A : Type ℓ}
    : ∀ (aa : list A) (idx : fin (length aa))
      , A
| [] (fin.mk idx ω) := begin apply false.rec, cases ω end
| (a :: aa) (fin.mk 0 ω) := a
| (a :: aa) (fin.mk (nat.succ idx) ω) := get aa { val := idx, is_lt := nat.lt_of_succ_lt_succ ω }

/-! #brief Length of append.
-/
@[simp] theorem {ℓ} length_append {A : Type ℓ}
    : ∀ {aa₁ aa₂ : list A}
      , length (aa₁ ++ aa₂) = length aa₁ + length aa₂
:= begin
     intros aa₁ aa₂,
     induction aa₁ with a₁ aa₁,
     { simp, apply rfl },
     calc length (a₁ :: aa₁ ++ aa₂)
              = length (a₁ :: (aa₁ ++ aa₂))     : rfl
          ... = length (aa₁ ++ aa₂) + 1         : rfl
          ... = length aa₁ + length aa₂ + 1     : by rw ih_1
          ... = (length aa₁ + 1) + length aa₂   : by simp
          ... = length (a₁ :: aa₁) + length aa₂ : rfl
   end
end list

/-! #brief Eliminating a fin 0.
-/
@[reducible] definition {ℓ} fin.zero_elim {A : Type ℓ}
    : fin 0 → A
| (fin.mk n ω)
:= begin apply false.cases_on, cases ω end

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
@[reducible] definition {ℓ} fin.enum {A : Type ℓ}
    : ∀ {N : ℕ} (f : fin N → A)
      , list A
| 0 f := []
| (nat.succ N) f
:= list.append
    (@fin.enum N (λ n, f { val := n^.val, is_lt := nat.less_than_or_equal.step n^.is_lt }))
    [ f { val := N, is_lt := nat.less_than_or_equal.refl _ } ]

/-! #brief The length of the enumeration.
-/
theorem {ℓ} fin.length_enum {A : Type ℓ}
    : ∀ {N : ℕ} {f : fin N → A}
      , list.length (fin.enum f) = N
| 0 f := rfl
| (nat.succ N) f
:= begin
     dsimp [fin.enum, fin.enum._main],
     apply eq.trans list.length_append,
     rw fin.length_enum,
     apply rfl
   end

/-! #brief fin.fn and fin.enum are inverses.
-/
@[simp] theorem {ℓ} fin.fn_enum {A : Type ℓ}
    : ∀ {N : ℕ} {f : fin N → A}
      , fin.fn (fin.enum f) = cast (by rw fin.length_enum) f
| 0 f := begin apply funext, intro n, apply fin.zero_elim n end
| (nat.succ N) f := sorry

-- A finite type.
structure {ℓ} FinType (T : Type ℓ) : Type (max 1 ℓ)
:= (card : ℕ)
   (of_n : fin card → T)
   (n_of : T → fin card)
   (n_of_n : ∀ {n : fin card}, n_of (of_n n) = n)
   (of_n_of : ∀ {t : T}, of_n (n_of t) = t)

-- A boxed finite type.
structure {ℓ} BxFinType : Type (ℓ + 1)
:= (T : Type ℓ)
   (is_finite : FinType T)

-- TODO: Fix docstring!
--/-! #brief poly_empty is a finite type.
---/
@[reducible] definition {ℓ} poly_empty.FinType
    : FinType poly_empty.{ℓ}
:= { card := 0
   , of_n := fin.zero_elim
   , n_of := poly_empty.elim
   , n_of_n := λ n, fin.zero_elim n
   , of_n_of := λ t, poly_empty.elim t
   }

/-! #brief poly_unit is a finite type.
-/
@[reducible] definition {ℓ} poly_unit.FinType
    : FinType poly_unit.{ℓ}
:= { card := 1
   , of_n := λ n, poly_unit.star
   , n_of := λ p, { val := 0, is_lt := by apply nat.less_than_or_equal.refl }
   , n_of_n := λ n, begin cases n, apply fin.eq_of_veq, induction val, apply rfl, cases is_lt, cases a end
   , of_n_of := λ t, eq.symm poly_unit.uniq
   }

/-! #brief poly_bool is a finite type.
-/
@[reducible] definition {ℓ} poly_bool.FinType
    : FinType poly_bool.{ℓ}
:= { card := 2
   , of_n := fin.fn (poly_bool.ff :: poly_bool.tt :: [])
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
