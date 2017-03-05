/- ----------------------------------------------------------------------------
Limits in LeanCat.
---------------------------------------------------------------------------- -/

import ..Cat

namespace qp
universe variables ℓobj ℓhom



/- ----------------------------------------------------------------------------
Limits.
---------------------------------------------------------------------------- -/

/-! #brief For certain type levels, LeanCat has all limits.
-/
instance LeanCat.HasAllLimits
    : HasAllLimits.{ℓobj ℓhom} LeanCat.{ℓobj}
:= { limit
      := λ {B : Cat.{ℓobj ℓhom}}
         , { limit
              := λ (F : B ⇉⇉ LeanCat.{ℓobj})
                 , { limit := Limit.mk F
                               { g : ∀ (b : [[B]]), F b // ∀ {b₁ b₂ : [[B]]} (f : b₁ →→ b₂), g b₂ = (F ↗ f) (g b₁) }
                               (λ b g, g^.elt_of b)
                               (λ cone c, { elt_of := λ b, cone^.hom b c
                                          , has_property := λ b₁ b₂ f, begin dsimp, rw cone^.triangle end
                                          })
                               (λ x₁ x₂ f, begin dsimp, apply pfunext, intro g, apply g^.has_property end)
                               (λ cone x, rfl)
                               (λ cone h, begin apply funext, intro c, exact sorry end)
                   }
           }
   }

end qp
