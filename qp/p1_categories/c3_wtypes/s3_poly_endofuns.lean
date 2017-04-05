/- -----------------------------------------------------------------------
Polynomial endofunctors.
----------------------------------------------------------------------- -/

import ..c2_limits
import .s2_algebras

namespace qp

open stdaux

universe variables ℓobjx ℓhomx ℓobj ℓhom



/- -----------------------------------------------------------------------
Polynomial endofunctors.
----------------------------------------------------------------------- -/

/-! #brief A dependent polynomial endofunctor.
-/
definition DepPolyEndoFun {C : Cat.{ℓobj ℓhom}}
    [C_HasDepProdFun : HasDepProdFun C]
    {a b c : C^.obj}
    (f : C^.hom a b)
    (h : C^.hom a c) [h_HasPullbacksAlong : HasPullbacksAlong C h]
    (g : C^.hom b c)
    : Fun (OverCat C c) (OverCat C c)
:= DepSumFun g □□ DepProdFun f □□ BaseChangeFun h

/-! #brief Preservation of co-limits by DepPolyEndoFun.
-/
definition DepPolyEndoFun.PresCoLimit {C : Cat.{ℓobj ℓhom}}
    [C_HasDepProdFun : HasDepProdFun C]
    {a b c : C^.obj}
    {f : C^.hom a b}
    {h : C^.hom a c} [h_HasPullbacksAlong : HasPullbacksAlong C h]
    {g : C^.hom b c} [g_HasPullbacksAlong : HasPullbacksAlong C g]
    {X : Cat.{ℓobjx ℓhomx}}
    (L : Fun X (OverCat C c))
    [f_PresCoLimitsFrom : PresCoLimitsFrom (DepProdFun f) X]
    : PresCoLimit L (DepPolyEndoFun f h g)
:= @PresCoLimit.comp _ _ _ _
     L
     (BaseChangeFun h)
     (Adj.left.PresCoLimit (BaseChange_DepProd.Adj h) L)
     (DepSumFun g □□ DepProdFun f)
     (@PresCoLimit.comp _ _ _ _
       (Fun.comp (BaseChangeFun h) L)
       (DepProdFun f) (PresCoLimitsFrom.pres_colimit (DepProdFun f) _)
       (DepSumFun g) (Adj.left.PresCoLimit (DepSum_BaseChange.Adj g) _))

/-! #brief Adámek's construction for dependent W-types.
-/
definition DepPolyEndoFun.Adamek {C : Cat.{ℓobj ℓhom}}
    [C_HasInit : HasInit C]
    [C_HasDepProdFun : HasDepProdFun C]
    {a b c : C^.obj} (f : C^.hom a b)
    [Cc_HasAllCoLimitsFrom : HasAllCoLimitsFrom (OverCat C c) NatCat]
    [f_PresCoLimitsFrom : PresCoLimitsFrom (DepProdFun f) NatCat]
    (h : C^.hom a c) [h_HasPullbacksAlong : HasPullbacksAlong C h]
    (g : C^.hom b c) [g_HasPullbacksAlong : HasPullbacksAlong C g]
    : HasInitAlg (DepPolyEndoFun f h g)
:= @Adamek (OverCat C c)
    (OverCat.HasInit C c)
    (DepPolyEndoFun f h g)
    (@HasAllCoLimitsFrom.has_colimit (OverCat C c) NatCat Cc_HasAllCoLimitsFrom
       (@AdamekFun (OverCat C c) (OverCat.HasInit C c) (DepPolyEndoFun f h g)))
    (@PresCoLimitsFrom.pres_colimit (OverCat C c) (OverCat C c)
       (DepPolyEndoFun f h g)
       NatCat
       { pres_colimit := λ L, DepPolyEndoFun.PresCoLimit L }
       (@AdamekFun (OverCat C c) (OverCat.HasInit C c) (DepPolyEndoFun f h g)))

/-! #brief A polynomial endofunctor.
-/
definition PolyEndoFun {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    [C_HasAllFinProducts : HasAllFinProducts C]
    [C_HasDepProdFun : HasDepProdFun C]
    {x y : C^.obj}
    (f : C^.hom x y)
    : Fun C C
:= OverFinal.from C
    □□ DepPolyEndoFun f (final_hom x) (final_hom y)
    □□ OverFinal.to C

/-! #brief Preservation of co-limits by PolyEndoFun.
-/
definition PolyEndoFun.PresCoLimit {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    [C_HasAllFinProducts : HasAllFinProducts C]
    [C_HasDepProdFun : HasDepProdFun C]
    {x y : C^.obj}
    {f : C^.hom x y}
    {X : Cat.{ℓobjx ℓhomx}}
    (L : Fun X C)
    [f_PresCoLimitsFrom : PresCoLimitsFrom (DepProdFun f) X]
    : PresCoLimit L (PolyEndoFun f)
:= @PresCoLimit.comp _ _ _ _
     L
     (OverFinal.to C)
     (sorry /- because OverFinal.to is a bijection -/)
     (OverFinal.from C □□ DepPolyEndoFun f (final_hom x) (final_hom y))
     (@PresCoLimit.comp _ _ _ _
       (OverFinal.to C □□ L)
       (DepPolyEndoFun f (final_hom x) (final_hom y)) (DepPolyEndoFun.PresCoLimit _)
       (OverFinal.from C) (sorry /- because OverFinal.from is a bijection -/))

/-! #brief Adámek's construction for W-types.
-/
definition PolyEndoFun.Adamek {C : Cat.{ℓobj ℓhom}}
    [C_HasInit : HasInit C]
    [C_HasFinal : HasFinal C]
    [C_HasAllFinProducts : HasAllFinProducts C]
    [C_HasDepProdFun : HasDepProdFun C]
    [C_HasAllCoLimitsFrom : HasAllCoLimitsFrom C NatCat]
    {x y : C^.obj} (f : C^.hom x y)
    [f_PresCoLimitsFrom : PresCoLimitsFrom (DepProdFun f) NatCat]
    : HasInitAlg (PolyEndoFun f)
:= @Adamek C
    C_HasInit
    (PolyEndoFun f)
    (@HasAllCoLimitsFrom.has_colimit C NatCat C_HasAllCoLimitsFrom
       (@AdamekFun C C_HasInit (PolyEndoFun f)))
    (@PresCoLimitsFrom.pres_colimit C C
       (PolyEndoFun f)
       NatCat
       { pres_colimit := λ L, PolyEndoFun.PresCoLimit L }
       (@AdamekFun C C_HasInit (PolyEndoFun f)))



/- -----------------------------------------------------------------------
W-types.
----------------------------------------------------------------------- -/

/-! #brief A W-type.
-/
@[class] definition HasWType (C : Cat.{ℓobj ℓhom})
    {b a : C^.obj} (disp : C^.hom b a)
:= ∀ [C_HasFinal : HasFinal C]
     [C_HasAllFinProducts : HasAllFinProducts C]
     [C_HasDepProdFun : HasDepProdFun C]
   , HasInitAlg (@PolyEndoFun C
                   C_HasFinal C_HasAllFinProducts C_HasDepProdFun
                   b a disp)

/-! #brief Adámek's construction for W-types.
-/
definition HasWType.Adamek (C : Cat.{ℓobj ℓhom})
    [C_HasInit : HasInit C]
    [C_HasAllCoLimitsFrom : HasAllCoLimitsFrom C NatCat]
    {b a : C^.obj} (disp : C^.hom b a)
    (f_PresCoLimitsFrom
      : HasDepProdFun C → PresCoLimitsFrom (DepProdFun disp) NatCat)
    : HasWType C disp
:= λ C_HasFinal C_HasAllFinProducts C_HasDepProdFun
   , @PolyEndoFun.Adamek C
       C_HasInit C_HasFinal
       C_HasAllFinProducts C_HasDepProdFun C_HasAllCoLimitsFrom
       b a disp
       (f_PresCoLimitsFrom C_HasDepProdFun)

/-! #brief The carrier of a W-type.
-/
definition wtype.carr {C : Cat.{ℓobj ℓhom}}
    [C_HasAllFinProducts : HasAllFinProducts C]
    [C_HasFinal : HasFinal C]
    [C_HasDepProdFun : HasDepProdFun C]
    {b a : C^.obj} (disp : C^.hom b a)
    [disp_HasWType : HasWType C disp]
    : C^.obj
:= @initalg.carr _ _ disp_HasWType

end qp
