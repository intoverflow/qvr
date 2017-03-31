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
