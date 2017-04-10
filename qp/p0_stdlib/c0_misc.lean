/- -----------------------------------------------------------------------
Misc facts about Lean.
----------------------------------------------------------------------- -/

namespace qp
namespace stdaux

/-! #brief funext, but for heterogeneous equality.
-/
theorem {ℓ₁ ℓ₂} hfunext
    : ∀ {A₁ A₂ : Type ℓ₁}
        {B : Type ℓ₂}
        {f₁ : A₁ → B} {f₂ : A₂ → B}
        (ωA : A₁ = A₂)
        (ω : ∀ (a : A₁), f₁ a = f₂ (cast ωA a))
      , f₁ == f₂
| A .(A) B f₁ f₂ (eq.refl .(A)) ω
:= begin
     apply heq_of_eq,
     apply funext,
     intro a,
     exact ω a
   end

/-! #brief The punit type is uniquely inhabited.
-/
theorem {ℓ} punit.uniq
    : ∀ (u₁ u₂ : punit.{ℓ})
      , u₁ = u₂
| punit.star punit.star := rfl

/-! #brief Equality helper for products.
-/
theorem {ℓ₁ ℓ₂} prod.eq {A : Type ℓ₁} {B : Type ℓ₂}
    : ∀ {ab₁ ab₂ : prod A B}
      , ab₁^.fst = ab₂^.fst
      → ab₁^.snd = ab₂^.snd
      → ab₁ = ab₂
| (prod.mk a b) (prod.mk .(a) .(b)) (eq.refl .(a)) (eq.refl .(b)) := rfl

/-! #brief The diagonal map.
-/
definition {ℓ} prod.diag {X : Type ℓ} (x : X)
    : prod X X
:= (x, x)

/-! #brief Max of two natural numbers.
-/
definition nat.max (a b : ℕ) : ℕ
:= if a ≤ b then b else a

theorem nat.le_max_left (a b : ℕ)
    : a ≤ nat.max a b
:= if ω : a ≤ b
    then begin
           unfold nat.max,
           rw if_pos ω,
           exact ω
         end
    else begin
           unfold nat.max,
           rw if_neg ω
         end

theorem nat.le_max_right (a b : ℕ)
    : b ≤ nat.max a b
:= if ω : a ≤ b
    then begin
           unfold nat.max,
           rw if_pos ω
         end
    else begin
           unfold nat.max,
           rw if_neg ω,
           exact le_of_not_le ω
         end

/-! #brief Handy absurd lemma.
-/
theorem nat.not_lt_add_left
    {P : Prop} (n : ℕ)
    : ∀ (m : ℕ) (ω : n + m < n)
      , P
| 0 ω := absurd ω (nat.lt_irrefl n)
| (nat.succ m) ω := nat.not_lt_add_left m
                     (by calc n + m < n + nat.succ m : nat.self_lt_succ _
                              ...   < n              : ω)

/-! #brief Handy absurd lemma.
-/
theorem nat.not_lt_add_right
    {P : Prop} (n : ℕ)
    : ∀ (m : ℕ) (ω : n + m < m)
      , P
| 0 ω := by cases ω
| (nat.succ m) ω := nat.not_lt_add_right m (nat.lt_of_succ_lt_succ ω)


/-! #brief The axiom of choice, for unique existance.
-/
noncomputable definition {ℓ} unique_choice {A : Type ℓ} {P : A → Prop}
    : (∃! (a : A), P a) → A
:= λ pr, classical.some (exists_of_exists_unique pr)

/-! #brief The axiom of unique choice satisfies the indicated property.
-/
theorem {ℓ} unique_choice.has_prop {A : Type ℓ} {P : A → Prop}
    (pr : ∃! (a : A), P a)
    : P (unique_choice pr)
:= classical.some_spec (exists_of_exists_unique pr)

/-! #brief The axiom of unique choice does what you'd think.
-/
theorem {ℓ} unique_choice.simp {A : Type ℓ} {P : A → Prop}
    {a : A} {ωa : P a} {ωP : ∀ (b : A), P b → b = a}
    : unique_choice (exists_unique.intro a ωa ωP) = a
:= begin
     apply ωP,
     apply unique_choice.has_prop
   end


end stdaux
end qp
