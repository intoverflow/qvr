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
