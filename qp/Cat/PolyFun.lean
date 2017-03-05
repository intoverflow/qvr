/- ----------------------------------------------------------------------------
Polynomial endofunctors.
---------------------------------------------------------------------------- -/

import .basic
import .Cone
import .Pullback
import .DepProduct
import .DepSum

namespace qp
universe variables ℓobj ℓhom



/- ----------------------------------------------------------------------------
Polynomial endofunctors.
---------------------------------------------------------------------------- -/

/-! #brief The polynomial endofunctor associated to a hom.
-/
definition PolyFunOf {C : Cat.{ℓobj ℓhom}}
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasAllDepProducts : HasAllDepProducts C]
    [C_HasFinal : HasFinal C]
    {x y : [[C]]}
    (f : x →→ y)
    : C ⇉⇉ C
:= UnsliceFun
   □□ DepSumFun final_hom
   □□ DepProdFun f
   □□ BaseChangeFun final_hom
   □□ SliceFinalFun C

/-! #brief A general polynomial endofunctor.
-/
class IsPolyFun {C : Cat.{ℓobj ℓhom}}
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasAllDepProducts : HasAllDepProducts C]
    [C_HasFinal : HasFinal C]
    (F : C ⇉⇉ C)
    : Type (max ℓobj ℓhom)
:= (dom : [[C]])
   (codom : [[C]])
   (hom : dom →→ codom)
   (to_poly : F ↣↣ PolyFunOf hom)
   (of_poly : PolyFunOf hom ↣↣ F)
   (iso : NatIso of_poly to_poly)

end qp
