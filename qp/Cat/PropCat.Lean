/- ----------------------------------------------------------------------------
Properties of PropCat.
---------------------------------------------------------------------------- -/

import .basic
import .Cone

namespace qp
universe variables ℓobj ℓhom



/- ----------------------------------------------------------------------------
Limits.
---------------------------------------------------------------------------- -/

/-! #brief PropCat has all limits at all type levels.
-/
definition PropCat.HasAllLimits
    : HasAllLimits PropCat
:= { limit
      := λ {B : Cat.{ℓobj ℓhom}} (F : B ⇉⇉ PropCat), ∀ (b : [[B]]), F b
   , is_limit
      := λ {B : Cat.{ℓobj ℓhom}} (F : B ⇉⇉ PropCat)
         , { is_cone := { proj := λ b g, g b
                        , proj_circ := λ b₁ b₂ f, rfl
                        }
           , is_final := { final := λ cone, { mediate := λ c, λ b, (cone b) c
                                            , factor := λ x, rfl
                                            }
                         , uniq := λ cone h, begin apply ConeHom.eq, apply rfl end
                         }
           }
   }

end qp
