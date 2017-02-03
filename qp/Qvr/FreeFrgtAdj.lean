/- ----------------------------------------------------------------------------
The adjunction between FreeCatFun and FrgtQvrFun.
---------------------------------------------------------------------------- -/

import .FreeCat
import .FrgtQvr

namespace qp
universe variables ℓobj ℓhom



/- ----------------------------------------------------------------------------
The adjunction between FreeCatFun and FrgtQvrFun.
---------------------------------------------------------------------------- -/

/-! #brief The adjunction between FreeCatFun and FrgtQvrFun.
-/
@[reducible] definition FreeCat_FrgtQvr_Adj
    : @Adj QvrCat.{ℓobj (max 1 ℓobj ℓhom)}
           CatCat.{ℓobj (max 1 ℓobj ℓhom)}
           FreeCatFun
           FrgtQvrFun
:= { counit := sorry
   , unit := sorry
   , id_left := sorry
   , id_right := sorry
   }

end qp
