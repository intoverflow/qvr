/- ----------------------------------------------------------------------------
Dependent sums.
---------------------------------------------------------------------------- -/

import .basic
import .Cone
import .Pullback

namespace qp
universe variables ℓobj ℓhom



/- ----------------------------------------------------------------------------
Dependent sums.
---------------------------------------------------------------------------- -/

/-! #brief The dependent sum functor.
-/
@[reducible] definition DepSumFun {C : Cat.{ℓobj ℓhom}}
    {x y : [[C]]}
    (base : x →→ y)
    [base_HasPullbacksAlong : HasAllPullbacksAlong C base]
    : SliceCat C x ⇉⇉ SliceCat C y
:= SliceCatFun C ↗ base

/-! #brief The dependent sum is left-adjoint to base change.
-/
@[reducible] definition DepSum_BaseChange.Adj {C : Cat.{ℓobj ℓhom}}
    {x y : [[C]]}
    {base : x →→ y}
    [base_HasPullbacksAlong : HasAllPullbacksAlong C base]
    : DepSumFun base ⊣ BaseChangeFun base
:= { unit := { component
                := λ X
                   , { hom := Pullback.into
                               (pullback_along base (base∘∘X^.hom))
                               X^.hom
                               ⟨⟨X^.dom⟩⟩
                               (eq.symm C^.circ_id_right)
                     , triangle := sorry
                     }
             , transport := λ X Y f, begin apply SliceHom.eq, exact sorry end
             }
   , counit := { component
                  := λ X
                     , { hom := Pullback.π₂ (pullback_along base X^.hom)
                       , triangle := begin exact sorry end
                       }
               , transport := begin exact sorry end
               }
   , id_left := begin exact sorry end
   , id_right := begin exact sorry end
   }

end qp
