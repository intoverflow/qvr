/- ----------------------------------------------------------------------------
Properties of LeanCat.
---------------------------------------------------------------------------- -/

import .basic
import .Cone

namespace qp
universe variables ℓ ℓobj ℓhom



/- ----------------------------------------------------------------------------
Limits.
---------------------------------------------------------------------------- -/

/-! #brief For certain universe levels, LeanCat has all limits.
-/
definition LeanCat.HasAllLimits
    : HasAllLimits LeanCat.{max 1 ℓobj ℓhom}
:= { limit
      := λ {B : Cat.{ℓobj ℓhom}} (F : B ⇉⇉ LeanCat.{max 1 ℓobj ℓhom})
         , { g : ∀ (b : [[B]]), F b // ∀ {b₁ b₂ : [[B]]} (f : b₁ →→ b₂), g b₂ = (F ↗ f) (g b₁) }
   , is_limit
      := λ {B : Cat.{ℓobj ℓhom}} (F : B ⇉⇉ LeanCat.{max 1 ℓobj ℓhom})
         , { is_cone := { proj := λ b g, g^.elt_of b
                        , proj_circ
                           := λ b₁ b₂ f
                              , begin
                                  dsimp, apply funext, intro g,
                                  apply g^.has_property
                                end
                        }
           , is_final := { final := λ cone, { mediate := λ c, ⟨ λ b, cone^.is_cone^.proj b c
                                                              , λ b₁ b₂ f, by rw cone^.is_cone^.proj_circ
                                                              ⟩
                                            , factor := λ x, rfl
                                            }
                         , uniq
                            := λ cone h
                               , begin
                                   apply ConeHom.eq,
                                   apply funext, intro c,
                                   apply subtype.eq,
                                   dsimp,
                                   apply funext, intro x,
                                   rw h^.factor
                                 end
                         }
           }
   }

end qp
