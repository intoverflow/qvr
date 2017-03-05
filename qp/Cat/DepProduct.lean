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
    (base : x →→ y)
    [base_HasPullbacksAlong : HasAllPullbacksAlong C base]
    : Type ((max ℓobj ℓhom) + 1)
:= (dprod : SliceCat C x ⇉⇉ SliceCat C y)
   (adj : BaseChangeFun base ⊣ dprod)



/- ----------------------------------------------------------------------------
Categories with dependent products.
---------------------------------------------------------------------------- -/

/-! #brief A category with dependent products.
-/
class HasAllDepProducts (C : Cat.{ℓobj ℓhom})
    : Type ((max ℓobj ℓhom) + 2)
:= (dprod : ∀ [C_HasAllPullbacks : HasAllPullbacks C] {x y : [[C]]} (base : x →→ y)
            , DepProduct C base)

/-! #brief The dependent product functor.
-/
definition DepProdFun {C : Cat.{ℓobj ℓhom}}
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasAllDepProducts : HasAllDepProducts C]
    {x y : [[C]]}
    (base : x →→ y)
    : SliceCat C x ⇉⇉ SliceCat C y
:= DepProduct.dprod (HasAllDepProducts.dprod base)

end qp
