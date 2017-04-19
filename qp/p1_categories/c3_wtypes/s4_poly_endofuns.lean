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
    [C_HasAllPullbacks : HasAllPullbacks C]
    {a b c₁ c₂ : C^.obj}
    (f : C^.hom a b)
    (h : C^.hom a c₁)
    (g : C^.hom b c₂)
    [C_HasDepProd : HasDepProd C f]
    : Fun (OverCat C c₁) (OverCat C c₂)
:= DepSumFun g □□ DepProdFun f □□ BaseChangeFun h

/-! #brief A dependent polynomial functor.
-/
structure IsDepPolyFun {C : Cat.{ℓobj ℓhom}}
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasDepProd : HasAllDepProd C]
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
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasDepProd : HasAllDepProd C]
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
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasDepProd : HasAllDepProd C]
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
definition PolyEndoFun.induce {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasDepProd : HasAllDepProd C]
    {x y : C^.obj}
    (f : C^.hom x y)
    : Fun C C
:= OverFinal.from C
    □□ DepPolyFun f (final_hom x) (final_hom y)
    □□ OverFinal.to C

/-! #brief PolyEndoFun is conjugate to DepPolyFun.
-/
theorem PolyEndoFun_conj_DepPolyFun {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasDepProd : HasAllDepProd C]
    {x y : C^.obj}
    (f : C^.hom x y)
    : OverFinal.to C □□ PolyEndoFun.induce f □□ OverFinal.from C
        = DepPolyFun f (final_hom x) (final_hom y)
:= let bij₂ := (OverFinal.Bij C)^.id₂
in begin
     dsimp [PolyEndoFun.induce],
     repeat { rw Fun.comp_assoc },
     rw bij₂,
     repeat { rw -Fun.comp_assoc },
     rw bij₂,
     rw [Fun.comp_id_left, Fun.comp_id_right]
   end

/-! #brief A polynomial endo-functor.
-/
structure PolyEndoFun (C : Cat.{ℓobj ℓhom})
    [C_HasFinal : HasFinal C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasDepProd : HasAllDepProd C]
:= (endo : Fun C C)
   (dom : C^.obj)
   (codom : C^.obj)
   (hom : C^.hom dom codom)
   (to_poly : NatTrans endo (PolyEndoFun.induce hom))
   (of_poly : NatTrans (PolyEndoFun.induce hom) endo)
   (iso : NatIso to_poly of_poly)

/-! #brief PolyEndoFun.induce is a polynomial endo-functor.
-/
definition PolyEndoFun.of_hom {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasDepProd : HasAllDepProd C]
    {x y : C^.obj}
    (f : C^.hom x y)
    : PolyEndoFun C
:= { endo := PolyEndoFun.induce f
   , dom := x
   , codom := y
   , hom := f
   , to_poly := NatTrans.id _
   , of_poly := NatTrans.id _
   , iso := NatIso.id
   }

/-! #brief IsPolyEndoFun casts along natural isomorphisms.
-/
definition NatIso.IsPolyEndoFun₁ {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasDepProd : HasAllDepProd C]
    (P₂ : PolyEndoFun C)
    {P₁ : Fun C C}
    {η₁₂ : NatTrans P₁ P₂^.endo} {η₂₁ : NatTrans P₂^.endo P₁}
    (η_iso : NatIso η₁₂ η₂₁)
    : PolyEndoFun C
:= { endo := P₁
   , dom := P₂^.dom
   , codom := P₂^.codom
   , hom := P₂^.hom
   , to_poly := NatTrans.comp P₂^.to_poly η₁₂
   , of_poly := NatTrans.comp η₂₁ P₂^.of_poly
   , iso := NatIso.comp P₂^.iso η_iso
   }

theorem NatIso.IsPolyEndoFun₁.endo {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasDepProd : HasAllDepProd C]
    {P₂ : PolyEndoFun C}
    {P₁ : Fun C C}
    {η₁₂ : NatTrans P₁ P₂^.endo} {η₂₁ : NatTrans P₂^.endo P₁}
    (η_iso : NatIso η₁₂ η₂₁)
    : (NatIso.IsPolyEndoFun₁ P₂ η_iso)^.endo = P₁
:= rfl

/-! #brief IsPolyEndoFun casts along natural isomorphisms.
-/
definition NatIso.IsPolyEndoFun₂ {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasDepProd : HasAllDepProd C]
    (P₁ : PolyEndoFun C)
    {P₂ : Fun C C}
    {η₁₂ : NatTrans P₁^.endo P₂} {η₂₁ : NatTrans P₂ P₁^.endo}
    (η_iso : NatIso η₁₂ η₂₁)
    : PolyEndoFun C
:= NatIso.IsPolyEndoFun₁ P₁ η_iso^.flip

theorem NatIso.IsPolyEndoFun₂.endo {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasDepProd : HasAllDepProd C]
    {P₁ : PolyEndoFun C}
    {P₂ : Fun C C}
    {η₁₂ : NatTrans P₁^.endo P₂} {η₂₁ : NatTrans P₂ P₁^.endo}
    (η_iso : NatIso η₁₂ η₂₁)
    : (NatIso.IsPolyEndoFun₂ P₁ η_iso)^.endo = P₂
:= rfl

-- /-! #brief Every polynomial endo-functor is a dependent polynomial functor.
-- -/
-- definition IsPolyEndoFun.IsDepPolyFun {C : Cat.{ℓobj ℓhom}}
--     [C_HasFinal : HasFinal C]
--     [C_HasDepProd : HasDepProd C]
--     [C_HasAllPullbacks : HasAllPullbacks C]
--     (P : Fun C C)
--     (P_IsPolyEndoFun : IsPolyEndoFun P)
--     : IsDepPolyFun (OverFinal.to C □□ P □□ OverFinal.from C)
-- := { dom := P_IsPolyEndoFun^.dom
--    , codom := P_IsPolyEndoFun^.codom
--    , hom := P_IsPolyEndoFun^.hom
--    , dom_out := final_hom P_IsPolyEndoFun^.dom
--    , codom_out := final_hom P_IsPolyEndoFun^.codom
--    , to_poly
--       := let trans := NatTrans.whisk_right
--                        (NatTrans.whisk_left (OverFinal.to C) P_IsPolyEndoFun^.to_poly)
--                        (OverFinal.from C)
--          in NatTrans.comp (NatTrans.cast (PolyEndoFun_conj_DepPolyFun _)) trans
--    , of_poly
--        := let trans := NatTrans.whisk_right
--                         (NatTrans.whisk_left (OverFinal.to C) P_IsPolyEndoFun^.of_poly)
--                         (OverFinal.from C)
--           in NatTrans.comp trans (NatTrans.cast (eq.symm (PolyEndoFun_conj_DepPolyFun _)))
--    , equiv
--       := { id₁ := let foo := P_IsPolyEndoFun^.equiv^.id₁
--                   in sorry
--          , id₂ := let foo := P_IsPolyEndoFun^.equiv^.id₂
--                   in sorry
--          }
--    }



/- -----------------------------------------------------------------------
Sums of polynomial endo-functors.
----------------------------------------------------------------------- -/

definition PolyEndoFun.fincoproduct.IsPolyEndoFun.to_poly {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasDepProd : HasAllDepProd C]
    [C_HasAllFinCoProducts : HasAllFinCoProducts C]
    (Ps : list (PolyEndoFun C))
    : NatTrans (fincoproduct (FunCat C C) (list.map PolyEndoFun.endo Ps))
               (PolyEndoFun.induce (fincoproduct.hom (HomsList.from_list PolyEndoFun.hom Ps)))
:= fincoproduct.univ
     (FunCat C C)
     (list.map PolyEndoFun.endo Ps)
     sorry

definition PolyEndoFun.fincoproduct.IsPolyEndoFun.of_poly {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasDepProd : HasAllDepProd C]
    [C_HasAllFinCoProducts : HasAllFinCoProducts C]
    (Ps : list (PolyEndoFun C))
    : NatTrans (PolyEndoFun.induce (fincoproduct.hom (HomsList.from_list PolyEndoFun.hom Ps)))
               (fincoproduct (FunCat C C) (list.map PolyEndoFun.endo Ps))
:= sorry

definition PolyEndoFun.fincoproduct.IsPolyEndoFun.iso {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasDepProd : HasAllDepProd C]
    [C_HasAllFinCoProducts : HasAllFinCoProducts C]
    (Ps : list (PolyEndoFun C))
    : NatIso (PolyEndoFun.fincoproduct.IsPolyEndoFun.to_poly Ps) 
             (PolyEndoFun.fincoproduct.IsPolyEndoFun.of_poly Ps)
:= sorry

/-! #brief Sum operation on polynomial endo-functors.
-/
definition PolyEndoFun.sum {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasDepProd : HasAllDepProd C]
    [C_HasAllFinCoProducts : HasAllFinCoProducts C]
    (Ps : list (PolyEndoFun C))
    : PolyEndoFun C
:= { endo := fincoproduct (FunCat C C) (list.map PolyEndoFun.endo Ps)
   , dom := _ -- fincoproduct C (list.map PolyEndoFun.dom Ps)
   , codom := _ -- fincoproduct C (list.map PolyEndoFun.codom Ps)
   , hom := fincoproduct.hom (HomsList.from_list PolyEndoFun.hom Ps)
   , to_poly := PolyEndoFun.fincoproduct.IsPolyEndoFun.to_poly Ps
   , of_poly := PolyEndoFun.fincoproduct.IsPolyEndoFun.of_poly Ps
   , iso := PolyEndoFun.fincoproduct.IsPolyEndoFun.iso Ps
   }

/-! #brief Iso for the domain of the sum.
-/
definition PolyEndoFun.sum.dom_iso {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasDepProd : HasAllDepProd C]
    [C_HasAllFinCoProducts : HasAllFinCoProducts C]
    (Ps : list (PolyEndoFun C))
    : C^.hom (fincoproduct C (list.map PolyEndoFun.dom Ps))
             (PolyEndoFun.sum Ps)^.dom
:= cast_hom begin dsimp [PolyEndoFun.sum], rw list.map_map end

/-! #brief Iso for the codomain of the sum.
-/
definition PolyEndoFun.sum.codom_iso {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasDepProd : HasAllDepProd C]
    [C_HasAllFinCoProducts : HasAllFinCoProducts C]
    (Ps : list (PolyEndoFun C))
    : C^.hom (PolyEndoFun.sum Ps)^.codom
             (fincoproduct C (list.map PolyEndoFun.codom Ps))
:= cast_hom begin dsimp [PolyEndoFun.sum], rw list.map_map end



/- -----------------------------------------------------------------------
Adámek's construction for polynomial endo-functors.
----------------------------------------------------------------------- -/

/-! #brief Preservation of co-limits by PolyEndoFun.
-/
definition PolyEndoFun.PresCoLimit {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasDepProd : HasAllDepProd C]
    {x y : C^.obj}
    {f : C^.hom x y}
    {X : Cat.{ℓobjx ℓhomx}}
    (L : Fun X C)
    [f_PresCoLimitsFrom : PresCoLimitsFrom (DepProdFun f) X]
    : PresCoLimit L (PolyEndoFun.induce f)
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
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasDepProd : HasAllDepProd C]
    [C_HasAllCoLimitsFrom : HasAllCoLimitsFrom C NatCat]
    {x y : C^.obj} (f : C^.hom x y)
    [f_PresCoLimitsFrom : PresCoLimitsFrom (DepProdFun f) NatCat]
    : HasInitAlg (PolyEndoFun.induce f)
:= @Adamek C
    C_HasInit
    (PolyEndoFun.induce f)
    (@HasAllCoLimitsFrom.has_colimit C NatCat C_HasAllCoLimitsFrom
       (@AdamekFun C C_HasInit (PolyEndoFun.induce f)))
    (@PresCoLimitsFrom.pres_colimit C C
       (PolyEndoFun.induce f)
       NatCat
       { pres_colimit := λ L, PolyEndoFun.PresCoLimit L }
       (@AdamekFun C C_HasInit (PolyEndoFun.induce f)))

end qp
