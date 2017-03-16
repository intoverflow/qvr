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
| A .A B f₁ f₂ (eq.refl .A) ω
:= begin
     apply heq_of_eq,
     apply funext,
     intro a,
     exact ω a
   end


end stdaux
end qp
