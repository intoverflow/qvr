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
    {base : x →→ y}
    (base_HasPullbacksAlong : HasAllPullbacksAlong C base)
    : SliceCat C x ⇉⇉ SliceCat C y
:= SliceFun C ↗ base

/-! #brief The dependent sum is left-adjoint to base change.
-/
@[reducible] definition DepSum_BaseChange.Adj {C : Cat.{ℓobj ℓhom}}
    {x y : [[C]]}
    {base : x →→ y}
    (base_HasPullbacksAlong : HasAllPullbacksAlong C base)
    : DepSumFun @base_HasPullbacksAlong ⊣ BaseChangeFun @base_HasPullbacksAlong
:= { unit := { component
                := λ X
                   , { hom := Pullback.into
                               (base_HasPullbacksAlong (base∘∘X^.hom))
                               X^.hom
                               ⟨⟨X^.dom⟩⟩
                               begin dsimp, simp end
                     , triangle := sorry
                     }
             , transport := λ X Y f, begin apply SliceCat.Hom.eq, exact sorry end
             }
   , counit := { component
                  := λ X
                     , { hom := Pullback.π₂ (base_HasPullbacksAlong X^.hom)
                       , triangle := begin exact sorry end
                       }
               , transport := begin exact sorry end
               }
   , id_left := begin exact sorry end
   , id_right := begin exact sorry end
   }

end qp
