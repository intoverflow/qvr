/- ----------------------------------------------------------------------------
W-types.
---------------------------------------------------------------------------- -/

import .basic
import .PolyFun
import .AlgFun

namespace qp
universe variables ℓobj ℓhom



/- ----------------------------------------------------------------------------
W-types.
---------------------------------------------------------------------------- -/

/-! #brief A W-type.
-/
@[reducible] definition WType {C : Cat.{ℓobj ℓhom}}
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasAllDepProducts : HasAllDepProducts C]
    [C_HasFinal : HasFinal C]
    (F : C ⇉⇉ C)
    [F_Poly : IsPolyFun F]
    : Type ((max ℓobj ℓhom) + 1)
:= Init (AlgFunCat F)



/- ----------------------------------------------------------------------------
Categories with W-types.
---------------------------------------------------------------------------- -/

/-! #brief A category with all W-types.
-/
class HasAllWTypes (C : Cat.{ℓobj ℓhom})
    : Type ((max ℓobj ℓhom) + 2)
:= (wtype : ∀ [C_HasAllPullbacks : HasAllPullbacks C]
              [C_HasAllDepProducts : HasAllDepProducts C]
              [C_HasFinal : HasFinal C]
              {F : C ⇉⇉ C}
              [F_Poly : IsPolyFun F]
            , WType F)

end qp
