/- -----------------------------------------------------------------------
Polynomial endofunctors.
----------------------------------------------------------------------- -/

import ..c2_limits
import .s1_algebras

namespace qp

open stdaux

universe variables ℓobj ℓhom



/- -----------------------------------------------------------------------
Polynomial endofunctors.
----------------------------------------------------------------------- -/

/-! #brief A dependent polynomial endofunctor.
-/
definition DepPolyEndoFun {C : Cat.{ℓobj ℓhom}}
    [C_HasDepProdFun : HasDepProdFun C]
    {a b c : C^.obj}
    (f : C^.hom a b) [f_HasPullbacksAlong : HasPullbacksAlong C f]
    (h : C^.hom a c) [h_HasPullbacksAlong : HasPullbacksAlong C h]
    (g : C^.hom b c)
    : Fun (OverCat C c) (OverCat C c)
:= DepSumFun g □□ DepProdFun f □□ BaseChangeFun h

/-! #brief A polynomial endofunctor.
-/
definition PolyEndoFun {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    [C_HasDepProdFun : HasDepProdFun C]
    {x y : C^.obj}
    (f : C^.hom x y) [f_HasPullbacksAlong : HasPullbacksAlong C f]
    [x_HasPullbacksAlong : HasPullbacksAlong C (final_hom x)]
    [y_HasPullbacksAlong : HasPullbacksAlong C (final_hom y)]
    : Fun C C
:= OverFinal.from C
    □□ DepPolyEndoFun f (final_hom x) (final_hom y)
    □□ OverFinal.to C



/- -----------------------------------------------------------------------
Polynomial endofunctors.
----------------------------------------------------------------------- -/

/-! #brief A W-type.
-/
@[class] definition HasWType (C : Cat.{ℓobj ℓhom})
    {x y : C^.obj} (f : C^.hom x y)
:= ∀ [C_HasFinal : HasFinal C]
     [C_HasDepProdFun : HasDepProdFun C]
     [f_HasPullbacksAlong : HasPullbacksAlong C f]
     [x_HasPullbacksAlong : HasPullbacksAlong C (@final_hom _ C_HasFinal x)]
     [y_HasPullbacksAlong : HasPullbacksAlong C (@final_hom _ C_HasFinal y)]
   , HasInitAlg (@PolyEndoFun _ C_HasFinal C_HasDepProdFun x y f f_HasPullbacksAlong x_HasPullbacksAlong y_HasPullbacksAlong)

/-! #brief The carrier of a W-type.
-/
definition wtype.carr {C : Cat.{ℓobj ℓhom}}
    {x y : C^.obj} (f : C^.hom x y)
    [f_HasWType : HasWType C f]
    [C_HasFinal : HasFinal C]
    [C_HasDepProdFun : HasDepProdFun C]
    [f_HasPullbacksAlong : HasPullbacksAlong C f]
    [x_HasPullbacksAlong : HasPullbacksAlong C (final_hom x)]
    [y_HasPullbacksAlong : HasPullbacksAlong C (final_hom y)]
    : C^.obj
:= @initalg.carr _ _ f_HasWType

end qp
