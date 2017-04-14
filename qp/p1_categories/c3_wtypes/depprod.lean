/- -----------------------------------------------------------------------
Dependent products.
----------------------------------------------------------------------- -/

import ..c1_basic
import ..c2_limits

namespace qp

open stdaux

universe variables ℓobj ℓhom



/- -----------------------------------------------------------------------
Dependent products.
----------------------------------------------------------------------- -/

/-! #brief The fiber held inside the dependent product object.
-/
definition Test.DepProdFun.obj.fiber {C : Cat.{ℓobj (ℓhom + 1)}}
    [C_HasFinal : HasFinal C]
    [C_HasAllProducts : HasAllProducts C]
    [C_HasAllCoProducts : HasAllCoProducts C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    {B A : C^.obj} (disp : C^.hom B A)
    (S : OverObj C B)
    (a : C^.hom (final C) A)
    (b : C^.hom (final C) (Fiber disp a))
    : C^.obj
:= Fiber S^.hom (Fiber.π _ _ ∘∘ b)

/-! #brief The product held inside the dependent product object.
-/
definition Test.DepProdFun.obj.product {C : Cat.{ℓobj (ℓhom + 1)}}
    [C_HasFinal : HasFinal C]
    [C_HasAllProducts : HasAllProducts C]
    [C_HasAllCoProducts : HasAllCoProducts C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    {B A : C^.obj} (disp : C^.hom B A)
    (S : OverObj C B)
    (a : C^.hom (final C) A)
    : C^.obj
:= @product C
      (C^.hom (final C) (Fiber disp a))    -- {b : B // disp b = a}
      (Test.DepProdFun.obj.fiber disp S a) -- { x : S^.obj // S^.hom x = b^.val})
      (HasAllProducts.HasProduct C _)

/-! #brief The dependent product functor on objects.
-/
definition Test.DepProdFun.obj {C : Cat.{ℓobj (ℓhom + 1)}}
    [C_HasFinal : HasFinal C]
    [C_HasAllProducts : HasAllProducts C]
    [C_HasAllCoProducts : HasAllCoProducts C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    {B A : C^.obj} (disp : C^.hom B A)
    (S : OverObj C B)
    : OverObj C A
:= { obj := @coproduct C (C^.hom (final C) A)
              (Test.DepProdFun.obj.product disp S)
              (HasAllCoProducts.HasCoProduct C _)
   , hom := coproduct.factor_out _
   }

/-! #brief Helper for the dependent product functor on homs.
-/
definition Test.DepProdFun.cone {C : Cat.{ℓobj (ℓhom + 1)}}
    [C_HasFinal : HasFinal C]
    [C_HasAllProducts : HasAllProducts C]
    [C_HasAllCoProducts : HasAllCoProducts C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    {B A : C^.obj} (disp : C^.hom B A)
    {S₀ S₁ : OverObj C B}
    (f : OverHom C B S₀ S₁)
    (a : C^.hom (final C) A)
    : ProductCone C (Test.DepProdFun.obj.fiber disp S₁ a)
:= (ProductCone.mk (Test.DepProdFun.obj.product disp S₀ a)
      (λ b, C^.circ
            (Fiber.hom f^.hom
              begin
                rw -f^.triangle,
                refine eq.trans _ 
                  (eq.trans (pullback.π_comm C _
                          --(S₀^.hom↗→(pullback.π C (disp↗→a↗→↗) (@fin_of 1 0) ∘∘ b)↗→↗)
                          (@fin_of 0 1) (@fin_of 1 0))
                          rfl),
                apply Cat.circ.congr_right,
                apply final_hom.uniq'
              end)
            (product.π C _ b)))

/-! #brief Helper for the dependent product functor on homs.
-/
definition Test.DepProdFun.cocone {C : Cat.{ℓobj (ℓhom + 1)}}
    [C_HasFinal : HasFinal C]
    [C_HasAllProducts : HasAllProducts C]
    [C_HasAllCoProducts : HasAllCoProducts C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    {B A : C^.obj} (disp : C^.hom B A)
    {S₀ S₁ : OverObj C B}
    (f : OverHom C B S₀ S₁)
    : CoProductCone C (Test.DepProdFun.obj.product disp S₀)
:= CoProductCone.mk (Test.DepProdFun.obj disp S₁)^.obj
      (λ a, C^.circ
              (coproduct.ι C _ a)
              (product.univ C (Test.DepProdFun.obj.fiber disp S₁ a)
                (Test.DepProdFun.cone disp f a)))

/-! #brief The dependent product functor on homs.
-/
definition Test.DepProdFun.hom {C : Cat.{ℓobj (ℓhom + 1)}}
    [C_HasFinal : HasFinal C]
    [C_HasAllProducts : HasAllProducts C]
    [C_HasAllCoProducts : HasAllCoProducts C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    {B A : C^.obj} (disp : C^.hom B A)
    {S₀ S₁ : OverObj C B}
    (f : OverHom C B S₀ S₁)
    : OverHom C A
       (Test.DepProdFun.obj disp S₀)
       (Test.DepProdFun.obj disp S₁)
:= { hom := coproduct.univ C (Test.DepProdFun.obj.product disp S₀)
             (Test.DepProdFun.cocone disp f)
   , triangle
      := begin
           apply eq.symm,
           refine coproduct.univ.uniq C (Test.DepProdFun.obj.product disp S₀) (CoProductCone.mk A (λ (a : ⟦C : final C →→ A⟧), a ∘∘ final_hom (Test.DepProdFun.obj.product disp S₀ a))) _ _,
           intro a,
           apply eq.symm,
           apply eq.trans (eq.symm C^.circ_assoc),
           apply eq.trans (Cat.circ.congr_right (eq.symm (coproduct.univ.mediates C (Test.DepProdFun.obj.product disp S₀) (Test.DepProdFun.cocone disp f) a))),
           apply eq.trans C^.circ_assoc,
           apply eq.trans (Cat.circ.congr_left (eq.symm (coproduct.univ.mediates C (Test.DepProdFun.obj.product disp S₁) (CoProductCone.mk A (λ (a : ⟦C : final C →→ A⟧), a ∘∘ final_hom (Test.DepProdFun.obj.product disp S₁ a))) a))),
           apply eq.trans (eq.symm C^.circ_assoc),
           apply Cat.circ.congr_right,
           apply final_hom.uniq
         end
   }

/-! #brief The dependent product functor.
-/
definition Test.DepProdFun {C : Cat.{ℓobj (ℓhom + 1)}}
    [C_HasFinal : HasFinal C]
    [C_HasAllProducts : HasAllProducts C]
    [C_HasAllCoProducts : HasAllCoProducts C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    {B A : C^.obj} (disp : C^.hom B A)
    : Fun (OverCat C B) (OverCat C A)
:= { obj := Test.DepProdFun.obj disp
   , hom := @Test.DepProdFun.hom C
              C_HasFinal
              C_HasAllProducts
              C_HasAllCoProducts
              C_HasAllPullbacks
              B A disp
   , hom_id
      := λ x
         , begin
             apply OverHom.eq,
             dsimp [Test.DepProdFun.hom],
             apply eq.symm,
             apply coproduct.univ.uniq C (Test.DepProdFun.obj.product disp x) (Test.DepProdFun.cocone disp ((OverCat C B)^.id x)),
             intro a,
             apply eq.symm,
             apply eq.trans C^.circ_id_left,
             apply eq.trans (eq.symm C^.circ_id_right),
             apply Cat.circ.congr_right,
             apply product.univ.uniq C (Test.DepProdFun.obj.fiber disp x a) (Test.DepProdFun.cone disp ((OverCat C B)^.id x) a),
             intro a',
             apply eq.symm,
             apply eq.trans C^.circ_id_right,
             apply eq.trans (eq.symm C^.circ_id_left),
             apply Cat.circ.congr_left,
             apply pullback.univ.uniq C _ (Fiber.cone _ _),
             { intro n,
               cases n with n ωb,
               cases n with n,
               { apply eq.trans C^.circ_id_left,
                 apply eq.symm,
                 apply eq.trans C^.circ_id_right,
                 trivial
               },
               cases n with n,
               { apply final_hom.uniq' },
               cases ωb with _ ωb',
               cases ωb' with _ ωb'',
               cases ωb''
             },
             { apply eq.symm,
               apply eq.trans C^.circ_id_right,
               exact sorry
             }
           end
   , hom_circ := sorry
   }

/-! #brief BaseChangeFun and DepProdFun are adjoint (hom of counit component).
-/
definition Test.BaseChange_DepProd.Adj.counit.com.hom {C : Cat.{ℓobj (ℓhom + 1)}}
    [C_HasFinal : HasFinal C]
    [C_HasAllProducts : HasAllProducts C]
    [C_HasAllCoProducts : HasAllCoProducts C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    {B A : C^.obj} (disp : C^.hom B A)
    (x : OverObj C B)
    (magic
      : ∀ (b : C^.hom ((BaseChangeFun disp □□ Test.DepProdFun disp)^.obj x)^.obj B)
          (a : C^.hom (final C) A)
        , C^.hom (Test.DepProdFun.obj.product disp x a) x^.obj)
    : C^.hom ((BaseChangeFun disp □□ Test.DepProdFun disp)^.obj x)^.obj
             x^.obj
-- := sorry
:= let pb₀ : C^.hom _ B -- ((BaseChangeFun disp □□ Test.DepProdFun disp)^.obj x)^.obj B
          := pullback.π C (disp ↗→ (Test.DepProdFun.obj disp x)^.hom ↗→↗) (@fin_of 1 0)
-- in let pcone : C^.hom (final C) A
--                → PullbackCone C (disp↗→((Test.DepProdFun.obj disp x)^.hom)↗→↗)
--             := λ a, PullbackCone.mk (disp↗→((Test.DepProdFun.obj disp x)^.hom)↗→↗)
--                      (final C)
--                      a
--                      (begin end ↗←
--                       (coproduct.ι C (Test.DepProdFun.obj.product disp x) a
--                        ∘∘ product.univ C (Test.DepProdFun.obj.fiber disp x a)
--                            (ProductCone.mk (final C) (λ b, begin end))) ↗←↗)
--                       --  coproduct.univ C (Test.DepProdFun.obj.product disp x)
--                       --    (CoProductCone.mk (final C) (λ a', final_hom _)) ↗←↗)
--                      begin end
in let ccone : CoProductCone C (Test.DepProdFun.obj.product disp x)
            := CoProductCone.mk x^.obj
                -- (magic pb₀)
                (λ a, sorry)
                -- (λ a, Fiber.π _ _
                --        ∘∘ product.π C (Test.DepProdFun.obj.fiber disp x a)
                --            (Fiber.into _ _
                --             (pb₀ ∘∘ begin end)-- pullback.univ C (disp↗→((Test.DepProdFun.obj disp x)^.hom)↗→↗) (pcone a))
                --             begin end))
in let pb₁ : C^.hom ((BaseChangeFun disp □□ Test.DepProdFun disp)^.obj x)^.obj
                    (@coproduct C (C^.hom (final C) A)
                      (Test.DepProdFun.obj.product disp x)
                      (HasAllCoProducts.HasCoProduct C _))
         := pullback.π C (disp ↗→ (Test.DepProdFun.obj disp x)^.hom ↗→↗) (@fin_of 0 1)
in coproduct.univ C (Test.DepProdFun.obj.product disp x) ccone
   ∘∘ pb₁
-- := C^.circ
--     (coproduct.univ C (λ (i : ⟦C : final C →→ A⟧), pullback C (disp↗→(i ∘∘ final_hom (Test.DepProdFun.obj.product disp x i))↗→↗))
--       (CoProductCone.mk x^.obj
--         (λ a, begin dsimp [Test.DepProdFun.obj.product], end)))
--         -- (λ a, Fiber.π _ _
--         --         ∘∘ product.π C (Test.DepProdFun.obj.fiber disp x a) (Fiber.into _ _ begin end begin end)
--         --         ∘∘ pullback.π C _ { val := 1, is_lt := cast begin trivial end (@fin_of 0 1)^.is_lt}))) -- (@fin_of 0 1))))
--     (pullback_coproduct.coproduct_pullback _ _ _)
-- := begin
-- dsimp [Fun.comp, BaseChangeFun, Test.DepProdFun],
-- dsimp [BaseChangeFun.obj, Test.DepProdFun.obj]
-- end
-- := (coproduct.univ C (Test.DepProdFun.obj.product disp x)
--       (CoProductCone.mk x^.obj
--         (λ a, Fiber.π _ _
--                ∘∘ product.π C (Test.DepProdFun.obj.fiber disp x a)
--                  (Fiber.into _ _ begin end begin end))))
--     ∘∘ (pullback.π C (disp↗→(coproduct.factor_out (Test.DepProdFun.obj.product disp x))↗→↗) (@fin_of 0 1))

/-! #brief BaseChangeFun and DepProdFun are adjoint (counit component).
-/
definition Test.BaseChange_DepProd.Adj.counit.com {C : Cat.{ℓobj (ℓhom + 1)}}
    [C_HasFinal : HasFinal C]
    [C_HasAllProducts : HasAllProducts C]
    [C_HasAllCoProducts : HasAllCoProducts C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    {B A : C^.obj} (disp : C^.hom B A)
    (x : OverObj C B)
    : (OverCat C B)^.hom
        ((BaseChangeFun disp □□ Test.DepProdFun disp)^.obj x)
        x
:= { hom := Test.BaseChange_DepProd.Adj.counit.com.hom disp x sorry
   , triangle := sorry
   }

/-! #brief BaseChangeFun and DepProdFun are adjoint (counit).
-/
definition Test.BaseChange_DepProd.Adj.counit {C : Cat.{ℓobj (ℓhom + 1)}}
    [C_HasFinal : HasFinal C]
    [C_HasAllProducts : HasAllProducts C]
    [C_HasAllCoProducts : HasAllCoProducts C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    {B A : C^.obj} (disp : C^.hom B A)
    : NatTrans
        (BaseChangeFun disp □□ Test.DepProdFun disp)
        (Fun.id (OverCat C B))
:= { com := Test.BaseChange_DepProd.Adj.counit.com disp
   , natural := sorry
   }

/-! #brief BaseChangeFun and DepProdFun are adjoint (hom of unit component).
-/
definition Test.BaseChange_DepProd.Adj.unit.com.hom {C : Cat.{ℓobj (ℓhom + 1)}}
    [C_HasFinal : HasFinal C]
    [C_HasAllProducts : HasAllProducts C]
    [C_HasAllCoProducts : HasAllCoProducts C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    {B A : C^.obj} (disp : C^.hom B A)
    (x : OverObj C A)
    : C^.hom x^.obj ((Test.DepProdFun disp □□ BaseChangeFun disp)^.obj x)^.obj
:= sorry

/-! #brief BaseChangeFun and DepProdFun are adjoint (unit component).
-/
definition Test.BaseChange_DepProd.Adj.unit.com {C : Cat.{ℓobj (ℓhom + 1)}}
    [C_HasFinal : HasFinal C]
    [C_HasAllProducts : HasAllProducts C]
    [C_HasAllCoProducts : HasAllCoProducts C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    {B A : C^.obj} (disp : C^.hom B A)
    (x : OverObj C A)
    : (OverCat C A)^.hom
        x
        ((Test.DepProdFun disp □□ BaseChangeFun disp)^.obj x)
:= { hom := Test.BaseChange_DepProd.Adj.unit.com.hom disp x
   , triangle := sorry
   }

/-! #brief BaseChangeFun and DepProdFun are adjoint (unit).
-/
definition Test.BaseChange_DepProd.Adj.unit {C : Cat.{ℓobj (ℓhom + 1)}}
    [C_HasFinal : HasFinal C]
    [C_HasAllProducts : HasAllProducts C]
    [C_HasAllCoProducts : HasAllCoProducts C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    {B A : C^.obj} (disp : C^.hom B A)
    : NatTrans
        (Fun.id (OverCat C A))
        (Test.DepProdFun disp □□ BaseChangeFun disp)
:= { com := Test.BaseChange_DepProd.Adj.unit.com disp
   , natural := sorry
   }

-- /-! #brief BaseChangeFun and DepProdFun are adjoint (left identity).
-- -/
-- definition Test.BaseChange_DepProd.Adj.id_left {C : Cat.{ℓobj (ℓhom + 1)}}
--     [C_HasFinal : HasFinal C]
--     [C_HasAllProducts : HasAllProducts C]
--     [C_HasAllCoProducts : HasAllCoProducts C]
--     [C_HasAllPullbacks : HasAllPullbacks C]
--     {B A : C^.obj} (disp : C^.hom B A)
--     (x : OverObj C A)
--     : Test.BaseChange_DepProd.Adj.counit.com.hom disp ((BaseChangeFun disp)^.obj x)
--        ∘∘ ((BaseChangeFun disp)^.hom (Test.BaseChange_DepProd.Adj.unit.com disp x))^.hom
--        = C^.id _
-- := sorry

-- /-! #brief BaseChangeFun and DepProdFun are adjoint (right identity).
-- -/
-- definition Test.BaseChange_DepProd.Adj.id_right {C : Cat.{ℓobj (ℓhom + 1)}}
--     [C_HasFinal : HasFinal C]
--     [C_HasAllProducts : HasAllProducts C]
--     [C_HasAllCoProducts : HasAllCoProducts C]
--     [C_HasAllPullbacks : HasAllPullbacks C]
--     {B A : C^.obj} (disp : C^.hom B A)
--     (x : OverObj C B)
--     : ((Test.DepProdFun disp)^.hom (Test.BaseChange_DepProd.Adj.counit.com disp x))^.hom
--         ∘∘ Test.BaseChange_DepProd.Adj.unit.com.hom disp ((Test.DepProdFun disp)^.obj x)
--         = C^.id _
-- := sorry

/-! #brief BaseChangeFun and DepProdFun are adjoint.
-/
definition Test.BaseChange_DepProd.Adj {C : Cat.{ℓobj (ℓhom + 1)}}
    [C_HasFinal : HasFinal C]
    [C_HasAllProducts : HasAllProducts C]
    [C_HasAllCoProducts : HasAllCoProducts C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    {B A : C^.obj} (disp : C^.hom B A)
    : Adj (@BaseChangeFun C B A disp (HasAllPullbacks.HasPullbacksAlong C disp))
          (Test.DepProdFun disp)
:= { counit := Test.BaseChange_DepProd.Adj.counit disp
   , unit := Test.BaseChange_DepProd.Adj.unit disp
   , id_left := λ x, OverHom.eq sorry -- (Test.BaseChange_DepProd.Adj.id_left disp x)
   , id_right := λ x, OverHom.eq sorry -- (Test.BaseChange_DepProd.Adj.id_right disp x)
   }

end qp
