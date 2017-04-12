/- -----------------------------------------------------------------------
Polynomial functors.
----------------------------------------------------------------------- -/

import ..c2_limits
import .s1_exp
import .s2_algebras

namespace qp

open stdaux

universe variables ℓobjx ℓhomx ℓobj ℓhom



/- -----------------------------------------------------------------------
Polynomial functors.
----------------------------------------------------------------------- -/

/-! #brief A dependent polynomial functor.
-/
definition DepPolyFun {C : Cat.{ℓobj ℓhom}}
    [C_HasDepProd : HasDepProd C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    {a b c₁ c₂ : C^.obj}
    (f : C^.hom a b)
    (h : C^.hom a c₁)
    (g : C^.hom b c₂)
    : Fun (OverCat C c₁) (OverCat C c₂)
:= DepSumFun g □□ DepProdFun f □□ BaseChangeFun h

/-! #brief Preservation of co-limits by DepPolyFun.
-/
definition DepPolyFun.PresCoLimit {C : Cat.{ℓobj ℓhom}}
    [C_HasDepProd : HasDepProd C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    {a b c₁ c₂ : C^.obj}
    {f : C^.hom a b}
    {h : C^.hom a c₁}
    {g : C^.hom b c₂}
    {X : Cat.{ℓobjx ℓhomx}}
    (L : Fun X (OverCat C c₁))
    [f_PresCoLimitsFrom : PresCoLimitsFrom (DepProdFun f) X]
    : PresCoLimit L (DepPolyFun f h g)
:= @PresCoLimit.comp _ _ _ _
     L
     (BaseChangeFun h)
     (Adj.left.PresCoLimit (BaseChange_DepProd.Adj h) L)
     (DepSumFun g □□ DepProdFun f)
     (@PresCoLimit.comp _ _ _ _
       (Fun.comp (BaseChangeFun h) L)
       (DepProdFun f) (PresCoLimitsFrom.PresCoLimit (DepProdFun f) _)
       (DepSumFun g) (Adj.left.PresCoLimit (DepSum_BaseChange.Adj g) _))

/-! #brief Adámek's construction for dependent W-types.
-/
definition DepPolyFun.Adamek {C : Cat.{ℓobj ℓhom}}
    [C_HasInit : HasInit C]
    [C_HasDepProd : HasDepProd C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    {a b c : C^.obj} (f : C^.hom a b)
    [Cc_HasAllCoLimitsFrom : HasAllCoLimitsFrom (OverCat C c) NatCat]
    [f_PresCoLimitsFrom : PresCoLimitsFrom (DepProdFun f) NatCat]
    (h : C^.hom a c)
    (g : C^.hom b c)
    : HasInitAlg (DepPolyFun f h g)
:= @Adamek (OverCat C c)
    (OverCat.HasInit C c)
    (DepPolyFun f h g)
    (@HasAllCoLimitsFrom.has_colimit (OverCat C c) NatCat Cc_HasAllCoLimitsFrom
       (@AdamekFun (OverCat C c) (OverCat.HasInit C c) (DepPolyFun f h g)))
    (@PresCoLimitsFrom.pres_colimit (OverCat C c) (OverCat C c)
       (DepPolyFun f h g)
       NatCat
       { pres_colimit := λ L, DepPolyFun.PresCoLimit L }
       (@AdamekFun (OverCat C c) (OverCat.HasInit C c) (DepPolyFun f h g)))

/-! #brief A polynomial endofunctor.
-/
definition PolyEndoFun {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    [C_HasDepProd : HasDepProd C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    {x y : C^.obj}
    (f : C^.hom x y)
    : Fun C C
:= OverFinal.from C
    □□ DepPolyFun f (final_hom x) (final_hom y)
    □□ OverFinal.to C

/-! #brief Preservation of co-limits by PolyEndoFun.
-/
definition PolyEndoFun.PresCoLimit {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    [C_HasDepProd : HasDepProd C]
    [C_HasAllPullbacks : HasAllPullbacks C]
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
     (OverFinal.from C □□ DepPolyFun f (final_hom x) (final_hom y))
     (@PresCoLimit.comp _ _ _ _
       (OverFinal.to C □□ L)
       (DepPolyFun f (final_hom x) (final_hom y)) (DepPolyFun.PresCoLimit _)
       (OverFinal.from C) (sorry /- because OverFinal.from is a bijection -/))

/-! #brief Adámek's construction for W-types.
-/
definition PolyEndoFun.Adamek {C : Cat.{ℓobj ℓhom}}
    [C_HasInit : HasInit C]
    [C_HasFinal : HasFinal C]
    [C_HasDepProd : HasDepProd C]
    [C_HasAllPullbacks : HasAllPullbacks C]
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
    [C_HasFinal : HasFinal C]
    [C_HasDepProd : HasDepProd C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    {b a : C^.obj} (disp : C^.hom b a)
:= HasInitAlg (PolyEndoFun disp)

/-! #brief Helper for showing that a function has a W-Type.
-/
definition HasWType.show (C : Cat.{ℓobj ℓhom})
    [C_HasFinal : HasFinal C]
    [C_HasDepProd : HasDepProd C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    {b a : C^.obj} (disp : C^.hom b a)
    (ty : C^.obj)
    (hom : C^.hom ((PolyEndoFun disp)^.obj ty) ty)
    (ini : ∀ (ty' : C^.obj)
             (hom' : C^.hom ((PolyEndoFun disp)^.obj ty') ty')
           , C^.hom ty ty')
    (ωcomm : ∀ (ty' : C^.obj)
               (hom' : C^.hom ((PolyEndoFun disp)^.obj ty') ty')
             , hom' ∘∘ (PolyEndoFun disp)^.hom (ini ty' hom')
                = ini ty' hom' ∘∘ hom)
    (ωuniq : ∀ (ty' : C^.obj)
               (hom' : C^.hom ((PolyEndoFun disp)^.obj ty') ty')
               (h : C^.hom ty ty')
               (ωh : hom' ∘∘ (PolyEndoFun disp)^.hom h
                      = h ∘∘ hom)
             , h = ini ty' hom')
    : HasWType C disp
:= HasInit.show
    { carr := ty
    , hom := hom
    }
    (λ X, { hom := ini X^.carr X^.hom
          , comm := ωcomm X^.carr X^.hom
          })
    (λ X h, EndoAlgHom.eq (ωuniq X^.carr X^.hom h^.hom h^.comm))


/-! #brief Adámek's construction for W-types.
-/
definition HasWType.Adamek (C : Cat.{ℓobj ℓhom})
    [C_HasInit : HasInit C]
    [C_HasFinal : HasFinal C]
    [C_HasDepProd : HasDepProd C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasAllCoLimitsFrom : HasAllCoLimitsFrom C NatCat]
    {b a : C^.obj} (disp : C^.hom b a)
    (f_PresCoLimitsFrom : PresCoLimitsFrom (DepProdFun disp) NatCat)
    : HasWType C disp
:= PolyEndoFun.Adamek disp

/-! #brief The carrier of a W-type.
-/
definition wtype.carr {C : Cat.{ℓobj ℓhom}}
    [C_HasAllFinProducts : HasAllFinProducts C]
    [C_HasFinal : HasFinal C]
    [C_HasDepProd : HasDepProd C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    {b a : C^.obj} (disp : C^.hom b a)
    [disp_HasWType : HasWType C disp]
    : C^.obj
:= @initalg.carr _ _ disp_HasWType

/-! #brief The structure hom of a W-type.
-/
definition wtype.hom {C : Cat.{ℓobj ℓhom}}
    [C_HasAllFinProducts : HasAllFinProducts C]
    [C_HasFinal : HasFinal C]
    [C_HasDepProd : HasDepProd C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    {b a : C^.obj} (disp : C^.hom b a)
    [disp_HasWType : HasWType C disp]
    : C^.hom ((PolyEndoFun disp)^.obj (wtype.carr disp)) (wtype.carr disp)
:= @initalg.hom _ _ disp_HasWType

end qp
