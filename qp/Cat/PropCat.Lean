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
@[reducible] definition PropCat.HasAllLimits
    : HasAllLimits.{ℓobj ℓhom} PropCat
:= { limit
      := λ {B : Cat.{ℓobj ℓhom}} (F : B ⇉⇉ PropCat), ∀ (b : [[B]]), F b
   , is_limit
      := λ {B : Cat.{ℓobj ℓhom}} (F : B ⇉⇉ PropCat)
         , { is_cone := { proj := λ b g, g b
                        , triangle := λ b₁ b₂ f, rfl
                        }
           , is_final := { final := λ cone, { mediate := λ c, λ b, (cone b) c
                                            , factor := λ x, rfl
                                            }
                         , uniq := λ cone h, begin apply ConeHom.eq, apply rfl end
                         }
           }
   }



/- ----------------------------------------------------------------------------
Initial and final objects.
---------------------------------------------------------------------------- -/

/-! #brief false is an initial object in PropCat.
-/
@[reducible] definition PropCat.init : IsInit PropCat false
:= { init := λ P, false.elim
   , uniq := λ P ω, rfl
   }

/-! #brief true is a final object in PropCat.
-/
@[reducible] definition PropCat.final : IsFinal PropCat true
:= { final := λ P ω, true.intro
   , uniq := λ P ω, rfl
   }

end qp
