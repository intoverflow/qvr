/- ----------------------------------------------------------------------------
Dependent products in LeanCat.
---------------------------------------------------------------------------- -/

import ..Cat
import .Pullback

namespace qp



/- ----------------------------------------------------------------------------
Dependent products.
---------------------------------------------------------------------------- -/

/-
/-! #brief The Lean categories have dependent products.
-/
@[reducible] definition {ℓ} LeanCat.HasAllDepProducts
    : HasAllDepProducts @LeanCat.HasAllPullbacks.{ℓ}
:= λ T₀ T₁ base
   , { dprod := { obj := λ x, { dom := {σ : LeanCat^.hom T₀ x^.dom // LeanCat^.circ x^.hom σ = LeanCat^.id T₀ }
                              , hom := λ σ, begin end -- λ σ, σ^.elt_of^.snd
                              }
                , hom := begin end
                , hom_id := begin end
                , hom_circ := begin end
                }
     , adj
        := { unit := { component := λ x, { hom := λ x₀, { elt_of := λ t₀, { elt_of := { fst := t₀, snd := x₀ }, has_property := begin end }
                                                        , has_property := rfl
                                                        }
                                         , triangle := begin end
                                         }
                     , transport := begin end
                     }
           , counit := { component := begin end
                       , transport := begin end
                       }
           , id_left := begin end
           , id_right := begin end
           }
     }
-/

end qp
