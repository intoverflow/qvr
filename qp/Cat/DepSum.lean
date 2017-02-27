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

-- A dependent sum.
structure DepSum (C : Cat.{ℓobj ℓhom})
    {x y : [[C]]}
    {base : x →→ y}
    (base_HasPullbacksAlong : HasAllPullbacksAlong C base)
    : Type ((max ℓobj ℓhom) + 1)
:= (dsum : SliceCat C x ⇉⇉ SliceCat C y)
   (adj : dsum ⊣ BaseChangeFun @base_HasPullbacksAlong)



/- ----------------------------------------------------------------------------
Categories with dependent sums.
---------------------------------------------------------------------------- -/

/-! #brief A category with dependent sums.
-/
@[reducible] definition HasAllDepSums {C : Cat.{ℓobj ℓhom}}
    (C_HasAllPullbacks : HasAllPullbacks C)
    : Type ((max ℓobj ℓhom) + 1)
:= ∀ {x y : [[C]]} (base : x →→ y)
   , DepSum C (@HasAllPullbacks.HasAllPullbacksAlong C @C_HasAllPullbacks x y base)

end qp
