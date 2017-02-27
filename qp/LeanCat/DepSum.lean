/- ----------------------------------------------------------------------------
Dependent sums in LeanCat.
---------------------------------------------------------------------------- -/

import ..Cat
import .Pullback

namespace qp



/- ----------------------------------------------------------------------------
Dependent sums.
---------------------------------------------------------------------------- -/

/-! #brief The Lean categories have dependent sums.
-/
@[reducible] definition {ℓ} LeanCat.HasAllDepSums
    : HasAllDepSums @LeanCat.HasAllPullbacks.{ℓ}
:= λ T₀ T₁ base
   , { dsum := SliceFun LeanCat ↗ base
     , adj
        := { unit := { component := λ x, { hom := λ x₀, { elt_of := { fst := x^.hom x₀, snd := x₀ }
                                                        , has_property := rfl
                                                        }
                                         , triangle := rfl
                                         }
                     , transport := λ x y f, begin apply SliceCat.Hom.eq, exact sorry end
                     }
           , counit := { component := λ x, { hom := Pullback.π₂ (LeanCat.HasAllPullbacks base x^.hom)
                                           , triangle := begin exact sorry end
                                           }
                       , transport := begin exact sorry end
                       }
           , id_left := begin exact sorry end
           , id_right := begin exact sorry end
           }
     }

end qp
