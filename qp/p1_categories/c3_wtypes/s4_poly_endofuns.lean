/- -----------------------------------------------------------------------
Polynomial functors.
----------------------------------------------------------------------- -/

import ..c2_limits
import .s1_base_change
import .s2_exp
import .s3_algebras

namespace qp

open stdaux

universe variables ℓobjx ℓhomx ℓobj ℓhom



/- -----------------------------------------------------------------------
Dependent polynomial functors.
----------------------------------------------------------------------- -/

/-! #brief An induced dependent polynomial functor.
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

/-! #brief A dependent polynomial functor.
-/
structure IsDepPolyFun {C : Cat.{ℓobj ℓhom}}
    [C_HasDepProd : HasDepProd C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    {c₁ c₂ : C^.obj}
    (P : Fun (OverCat C c₁) (OverCat C c₂))
:= (dom : C^.obj)
   (codom : C^.obj)
   (hom : C^.hom dom codom)
   (dom_out : C^.hom dom c₁)
   (codom_out : C^.hom codom c₂)
   (to_poly : NatTrans P (DepPolyFun hom dom_out codom_out))
   (of_poly : NatTrans (DepPolyFun hom dom_out codom_out) P)
   (equiv : NatIso to_poly of_poly)

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



/- -----------------------------------------------------------------------
Polynomial endo-functors.
----------------------------------------------------------------------- -/

/-! #brief An induced polynomial endo-functor.
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

theorem PolyEndoFun.isDepPolyFun {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    [C_HasDepProd : HasDepProd C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    {x y : C^.obj}
    (f : C^.hom x y)
    : OverFinal.to C □□ PolyEndoFun f □□ OverFinal.from C
        = DepPolyFun f (final_hom x) (final_hom y)
:= let bij₂ := (OverFinal.Bij C)^.id₂
in begin
     dsimp [PolyEndoFun],
     repeat { rw Fun.comp_assoc },
     rw bij₂,
     repeat { rw -Fun.comp_assoc },
     rw bij₂,
     rw [Fun.comp_id_left, Fun.comp_id_right]
   end

/-! #brief A polynomial endo-functor.
-/
structure IsPolyEndoFun {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    [C_HasDepProd : HasDepProd C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    (P : Fun C C)
:= (dom : C^.obj)
   (codom : C^.obj)
   (hom : C^.hom dom codom)
   (to_poly : NatTrans P (PolyEndoFun hom))
   (of_poly : NatTrans (PolyEndoFun hom) P)
   (equiv : NatIso to_poly of_poly)

/-! #brief Every polynomial endo-functor is a dependent polynomial functor.
-/
definition IsPolyEndoFun.IsDepPolyFun {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    [C_HasDepProd : HasDepProd C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    (P : Fun C C)
    (P_IsPolyEndoFun : IsPolyEndoFun P)
    : IsDepPolyFun (OverFinal.to C □□ P □□ OverFinal.from C)
:= { dom := P_IsPolyEndoFun^.dom
   , codom := P_IsPolyEndoFun^.codom
   , hom := P_IsPolyEndoFun^.hom
   , dom_out := final_hom P_IsPolyEndoFun^.dom
   , codom_out := final_hom P_IsPolyEndoFun^.codom
   , to_poly
      := let trans := NatTrans.whisk_right
                       (NatTrans.whisk_left (OverFinal.to C) P_IsPolyEndoFun^.to_poly)
                       (OverFinal.from C)
         in NatTrans.comp (NatTrans.cast (PolyEndoFun.isDepPolyFun _)) trans
   , of_poly
       := let trans := NatTrans.whisk_right
                        (NatTrans.whisk_left (OverFinal.to C) P_IsPolyEndoFun^.of_poly)
                        (OverFinal.from C)
          in NatTrans.comp trans (NatTrans.cast (eq.symm (PolyEndoFun.isDepPolyFun _)))
   , equiv
      := { id₁ := let foo := P_IsPolyEndoFun^.equiv^.id₁
                  in sorry
         , id₂ := let foo := P_IsPolyEndoFun^.equiv^.id₂
                  in sorry
         }
   }

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
     (Adj.left.PresCoLimit (OverFinal.Bij C)^.Adj L)
     (OverFinal.from C □□ DepPolyFun f (final_hom x) (final_hom y))
     (@PresCoLimit.comp _ _ _ _
       (OverFinal.to C □□ L)
       (DepPolyFun f (final_hom x) (final_hom y)) (DepPolyFun.PresCoLimit _)
       (OverFinal.from C)
       (Adj.left.PresCoLimit (OverFinal.Bij C)^.flip^.Adj _))

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

end qp
