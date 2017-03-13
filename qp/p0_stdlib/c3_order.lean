/- -----------------------------------------------------------------------
Facts about orders.
----------------------------------------------------------------------- -/

namespace qp
namespace stdaux

universe variables ℓ₁ ℓ₂

/-! #brief A monotone function.
-/
definition monotone
    {A : Sort ℓ₁} (r : A → A → Prop)
    {B : Sort ℓ₂} (s : B → B → Prop)
    (f : A → B)
    : Prop
:= ∀ (a₁ a₂ : A)
   , r a₁ a₂
   → s (f a₁) (f a₂)

/-! #brief The identity function is monotone.
-/
definition id.monotone
    {A : Sort ℓ₁} (r : A → A → Prop)
    : monotone r r id
:= λ a₁ a₂ ω, ω

end stdaux
end qp
