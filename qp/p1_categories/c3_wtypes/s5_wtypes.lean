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
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasDepProd : HasAllDepProd C]
    (P : PolyEndoFun C)
:= HasInitAlg P^.endo

/-! #brief Helper for showing that a function has a W-Type.
-/
definition HasWType.show (C : Cat.{ℓobj ℓhom})
    [C_HasFinal : HasFinal C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasDepProd : HasAllDepProd C]
    (P : PolyEndoFun C)
    (ty : C^.obj)
    (hom : C^.hom (P^.endo^.obj ty) ty)
    (ini : ∀ (ty' : C^.obj)
             (hom' : C^.hom (P^.endo^.obj ty') ty')
           , C^.hom ty ty')
    (ωcomm : ∀ (ty' : C^.obj)
               (hom' : C^.hom (P^.endo^.obj ty') ty')
             , hom' ∘∘ P^.endo^.hom (ini ty' hom')
                = ini ty' hom' ∘∘ hom)
    (ωuniq : ∀ (ty' : C^.obj)
               (hom' : C^.hom (P^.endo^.obj ty') ty')
               (h : C^.hom ty ty')
               (ωh : hom' ∘∘ P^.endo^.hom h
                      = h ∘∘ hom)
             , h = ini ty' hom')
    : HasWType C P
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
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasDepProd : HasAllDepProd C]
    [C_HasAllCoLimitsFrom : HasAllCoLimitsFrom C NatCat]
    (P : PolyEndoFun C)
    (f_PresCoLimitsFrom : PresCoLimitsFrom (DepProdFun P^.hom) NatCat)
    : HasWType C P
:= NatIso.EndoAlgBij.HasInitAlg₁ (PolyEndoFun.Adamek P^.hom) P^.iso

/-! #brief The carrier of a W-type.
-/
definition wtype.carr {C : Cat.{ℓobj ℓhom}}
    [C_HasAllFinProducts : HasAllFinProducts C]
    [C_HasFinal : HasFinal C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasDepProd : HasAllDepProd C]
    (P : PolyEndoFun C)
    [P_HasWType : HasWType C P]
    : C^.obj
:= @initalg.carr _ _ P_HasWType

/-! #brief The structure hom of a W-type.
-/
definition wtype.fold {C : Cat.{ℓobj ℓhom}}
    [C_HasAllFinProducts : HasAllFinProducts C]
    [C_HasFinal : HasFinal C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasDepProd : HasAllDepProd C]
    (P : PolyEndoFun C)
    [P_HasWType : HasWType C P]
    : C^.hom (P^.endo^.obj (wtype.carr P)) (wtype.carr P)
:= @initalg.hom C P^.endo P_HasWType

/-! #brief The inverse of the structure hom of a W-type.
-/
definition wtype.unfold {C : Cat.{ℓobj ℓhom}}
    [C_HasAllFinProducts : HasAllFinProducts C]
    [C_HasFinal : HasFinal C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasDepProd : HasAllDepProd C]
    (P : PolyEndoFun C)
    [P_HasWType : HasWType C P]
    : C^.hom (wtype.carr P) (P^.endo^.obj (wtype.carr P))
:= @initalg.unhom C P^.endo P_HasWType

/-! #brief hom and elim are isos.
-/
definition wtype.iso {C : Cat.{ℓobj ℓhom}}
    [C_HasAllFinProducts : HasAllFinProducts C]
    [C_HasFinal : HasFinal C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasDepProd : HasAllDepProd C]
    (P : PolyEndoFun C)
    [P_HasWType : HasWType C P]
    : Iso (wtype.fold P) (wtype.unfold P)
:= @initalg.iso C P^.endo P_HasWType

end qp
