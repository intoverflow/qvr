/- -----------------------------------------------------------------------
W-types.
----------------------------------------------------------------------- -/

import .s4_poly_endofuns

namespace qp

open stdaux

universe variables ℓobj ℓhom



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
:= @initalg.hom C (PolyEndoFun disp) disp_HasWType

/-! #brief The inverse of the structure hom of a W-type.
-/
definition wtype.elim {C : Cat.{ℓobj ℓhom}}
    [C_HasAllFinProducts : HasAllFinProducts C]
    [C_HasFinal : HasFinal C]
    [C_HasDepProd : HasDepProd C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    {b a : C^.obj} (disp : C^.hom b a)
    [disp_HasWType : HasWType C disp]
    : C^.hom (wtype.carr disp) ((PolyEndoFun disp)^.obj (wtype.carr disp))
:= @initalg.unhom C (PolyEndoFun disp) disp_HasWType

/-! #brief hom and elim are isos.
-/
definition wtype.iso {C : Cat.{ℓobj ℓhom}}
    [C_HasAllFinProducts : HasAllFinProducts C]
    [C_HasFinal : HasFinal C]
    [C_HasDepProd : HasDepProd C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    {b a : C^.obj} (disp : C^.hom b a)
    [disp_HasWType : HasWType C disp]
    : Iso (wtype.hom disp) (wtype.elim disp)
:= @initalg.iso C (PolyEndoFun disp) disp_HasWType

end qp
