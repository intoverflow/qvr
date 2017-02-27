/- ----------------------------------------------------------------------------
Dependent products.
---------------------------------------------------------------------------- -/

import .basic
import .Cone
import .Pullback

namespace qp
universe variables ℓobj ℓhom



/- ----------------------------------------------------------------------------
Dependent products.
---------------------------------------------------------------------------- -/

-- A dependent product.
structure DepProduct (C : Cat.{ℓobj ℓhom})
    {x y : [[C]]}
    {base : x →→ y}
    (base_HasPullbacksAlong : HasAllPullbacksAlong C base)
    : Type ((max ℓobj ℓhom) + 1)
:= (dprod : SliceCat C x ⇉⇉ SliceCat C y)
   (adj : BaseChangeFun @base_HasPullbacksAlong ⊣ dprod)



/- ----------------------------------------------------------------------------
Categories with dependent products.
---------------------------------------------------------------------------- -/

/-! #brief A category with dependent products.
-/
@[reducible] definition HasAllDepProducts {C : Cat.{ℓobj ℓhom}}
    (C_HasAllPullbacks : HasAllPullbacks C)
    : Type ((max ℓobj ℓhom) + 1)
:= ∀ {x y : [[C]]} (base : x →→ y)
   , DepProduct C (@HasAllPullbacks.HasAllPullbacksAlong C @C_HasAllPullbacks x y base)

end qp
