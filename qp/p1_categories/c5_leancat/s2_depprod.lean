/- -----------------------------------------------------------------------
Dependent products in LeanCat.
----------------------------------------------------------------------- -/

import ..c1_basic
import ..c2_limits
import ..c3_wtypes

import .s1_basic

namespace qp

open stdaux

universe variables ℓ ℓobjx ℓhomx



/- -----------------------------------------------------------------------
The dependent product functor.
----------------------------------------------------------------------- -/

/-! #brief The dependent product functor on objects.
-/
definition LeanCat.DepProdFun.obj {B A : LeanCat.{ℓ}^.obj}
    (disp : LeanCat.{ℓ}^.hom B A)
    (S : OverObj LeanCat.{ℓ} B)
    : OverObj LeanCat.{ℓ} A
:= { obj := @coproduct LeanCat A
              (λ a, @product LeanCat {b : B // disp b = a}
                      (λ b, { x : S^.obj // S^.hom x = b^.val})
                      (LeanCat.HasProduct.{ℓ ℓ} _))
              (LeanCat.HasCoProduct.{ℓ ℓ} _)
   , hom := sigma.fst
   }

-- /-! #brief Function induced toward the dependent product of a monic.
-- -/
-- definition LeanCat.DepProdFun.obj.monic_to {B A : LeanCat.{ℓ}^.obj}
--     (disp : LeanCat.{ℓ}^.hom B A)
--     [disp_Monic : @Monic LeanCat.{ℓ} B A disp]
--     (S : OverObj LeanCat.{ℓ} B)
--     (s : S^.obj)
--     : (LeanCat.DepProdFun.obj disp S)^.obj
-- := { fst := disp (S^.hom s)
--    , snd := λ b
--             , { val := s
--               , property := eq.symm (LeanCat.Monic.inj disp_Monic b^.property)
--               }
--    }

-- /-! #brief Function induced from the dependent product of a (strong) epic.
-- -/
-- definition LeanCat.DepProdFun.obj.epic_from.upon {B A : LeanCat.{ℓ}^.obj}
--     (disp : LeanCat.{ℓ}^.hom B A)
--     (undisp : LeanCat.{ℓ}^.hom A B)
--     {ωdisp_undisp : LeanCat.{ℓ}^.circ disp undisp = LeanCat.{ℓ}^.id A}
--     (S : OverObj LeanCat.{ℓ} B)
--     (af : (LeanCat.DepProdFun.obj disp S)^.obj)
--     : {b // disp b = af^.fst}
-- := { val := undisp af^.fst
--    , property := congr_fun ωdisp_undisp af^.fst
--    }

-- /-! #brief Function induced from the dependent product of a (strong) epic.
-- -/
-- definition LeanCat.DepProdFun.obj.epic_from {B A : LeanCat.{ℓ}^.obj}
--     (disp : LeanCat.{ℓ}^.hom B A)
--     (undisp : LeanCat.{ℓ}^.hom A B)
--     (ωdisp_undisp : LeanCat.{ℓ}^.circ disp undisp = LeanCat.{ℓ}^.id A)
--     (S : OverObj LeanCat.{ℓ} B)
--     (af : (LeanCat.DepProdFun.obj disp S)^.obj)
--     : S^.obj
-- := (af^.snd (@LeanCat.DepProdFun.obj.epic_from.upon B A disp undisp ωdisp_undisp S af))^.val

-- /-! #brief The dependent product functor is trivial on isos.
-- -/
-- definition LeanCat.DepProdFun.obj.Iso {B A : LeanCat.{ℓ}^.obj}
--     (disp : LeanCat.{ℓ}^.hom B A)
--     [disp_Monic : @Monic LeanCat.{ℓ} B A disp]
--     (undisp : LeanCat.{ℓ}^.hom A B)
--     (ωdisp_undisp : LeanCat.{ℓ}^.circ disp undisp = LeanCat.{ℓ}^.id A)
--     (S : OverObj LeanCat.{ℓ} B)
--     : @Iso LeanCat.{ℓ} _ _
--         (LeanCat.DepProdFun.obj.monic_to disp S)
--         (LeanCat.DepProdFun.obj.epic_from disp undisp ωdisp_undisp S)
-- := { id₁ := rfl
--    , id₂ := begin
--               apply funext,
--               intro a,
--               cases a with a f,
--               unfold LeanCat SortCat,
--               dsimp,
--               unfold LeanCat.DepProdFun.obj.monic_to,
--               unfold LeanCat.DepProdFun.obj.epic_from,
--               exact sorry
--             end
--    }

/-! #brief The dependent product functor on functions.
-/
definition LeanCat.DepProdFun.hom {B A : LeanCat.{ℓ}^.obj}
    (disp : LeanCat.{ℓ}^.hom B A)
    {S₀ S₁ : OverObj LeanCat.{ℓ} B}
    (f : OverHom LeanCat.{ℓ} B S₀ S₁)
    : OverHom LeanCat.{ℓ} A
       (@LeanCat.DepProdFun.obj B A disp S₀)
       (@LeanCat.DepProdFun.obj B A disp S₁)
:= let a : (LeanCat.DepProdFun.obj disp S₀)^.obj → A
        := λ σ
           , σ^.fst
in let s₁ : ∀ (σ : (LeanCat.DepProdFun.obj disp S₀)^.obj)
              (b : {b // disp b = a σ})
            , S₁^.obj
         := λ σ b
            , f^.hom (σ^.snd b)^.val
in let ωs₁ : ∀ (σ : (LeanCat.DepProdFun.obj disp S₀)^.obj)
               (b : {b // disp b = a σ})
             , S₁^.hom (s₁ σ b) = b^.val
          := λ σ b
             , begin
                 apply eq.trans (congr_fun (eq.symm f^.triangle) (σ^.snd b)),
                 apply (σ^.snd b)^.property
               end
in { hom
      := λ σ, { fst := a σ
              , snd := λ b, { val := s₁ σ b, property := ωs₁ σ b }
              }
   , triangle := rfl
   }

/-! #brief The dependent product functor preserves identity functions.
-/
definition LeanCat.DepProdFun.hom_id {B A : LeanCat.{ℓ}^.obj}
    (disp : LeanCat.{ℓ}^.hom B A)
    (S : OverObj LeanCat.{ℓ} B)
    : LeanCat.DepProdFun.hom disp (OverHom.id LeanCat.{ℓ} B S)
       = OverHom.id LeanCat.{ℓ} A (LeanCat.DepProdFun.obj disp S)
:= begin
     apply OverHom.eq,
     apply funext, intro σ,
     cases σ with a f,
     apply congr_arg (sigma.mk a),
     apply funext, intro b,
     apply subtype.eq,
     trivial
   end

/-! #brief The dependent product functor distributes over composition.
-/
definition LeanCat.DepProdFun.hom_comp {B A : LeanCat.{ℓ}^.obj}
    (disp : LeanCat.{ℓ}^.hom B A)
    (S₁ S₂ S₃ : OverObj LeanCat.{ℓ} B)
    (g : OverHom LeanCat.{ℓ} B S₂ S₃)
    (f : OverHom LeanCat.{ℓ} B S₁ S₂)
    : LeanCat.DepProdFun.hom disp (OverHom.comp LeanCat.{ℓ} B _ _ _ g f)
       = OverHom.comp LeanCat.{ℓ} A _ _ _ (LeanCat.DepProdFun.hom disp g) (LeanCat.DepProdFun.hom disp f)
:= begin
     apply OverHom.eq,
     apply funext, intro σ,
     cases σ with a h,
     apply congr_arg (sigma.mk a),
     apply funext, intro b,
     apply subtype.eq,
     trivial
   end


/-! #brief The dependent product functor.
-/
definition LeanCat.DepProdFun {B A : LeanCat.{ℓ}^.obj}
    (disp : LeanCat.{ℓ}^.hom B A)
    : Fun (OverCat LeanCat.{ℓ} B) (OverCat LeanCat.{ℓ} A)
:= { obj := LeanCat.DepProdFun.obj disp
   , hom := @LeanCat.DepProdFun.hom B A disp
   , hom_id := LeanCat.DepProdFun.hom_id disp
   , hom_circ := LeanCat.DepProdFun.hom_comp disp
   }



-- /- -----------------------------------------------------------------------
-- The dependent product functor is right adjoint to base change.
-- ----------------------------------------------------------------------- -/

/-! #brief Component of the counit of the BaseChangeFun/LeanCat.DepProdFun adjunction.
-/
definition LeanCat.BaseChange_DepProd.Adj.counit_com
    {x y : LeanCat.{ℓ}^.obj}
    (f : LeanCat.{ℓ}^.hom x y)
    [f_HasPullbacksAlong : HasPullbacksAlong LeanCat.{ℓ} f]
    (X : OverObj LeanCat.{ℓ} x)
    : OverHom LeanCat.{ℓ} x
        (BaseChangeFun.obj f (LeanCat.DepProdFun.obj f X))
        X
:= sorry
-- := { hom := let pb₀ := pullback.π LeanCat.{ℓ} (f ↗→ (LeanCat.DepProdFun.obj f X)^.hom ↗→↗) (@fin_of 1 0)
--          in let pb₁ := pullback.π LeanCat.{ℓ} (f ↗→ (LeanCat.DepProdFun.obj f X)^.hom ↗→↗) (@fin_of 0 1)
--             in λ Z, ((pb₁ Z)^.snd { val := pb₀ Z, property := sorry })^.val
--    , triangle := sorry
--    }

/-! #brief Counit of the BaseChangeFun/LeanCat.DepProdFun adjunction.
-/
definition LeanCat.BaseChange_DepProd.Adj.counit
    {x y : LeanCat.{ℓ}^.obj}
    (f : LeanCat.{ℓ}^.hom x y)
    [f_HasPullbacksAlong : HasPullbacksAlong LeanCat.{ℓ} f]
    : NatTrans (@BaseChangeFun LeanCat.{ℓ} x y f f_HasPullbacksAlong □□ LeanCat.DepProdFun f)
               (Fun.id (OverCat LeanCat.{ℓ} x))
:= { com := LeanCat.BaseChange_DepProd.Adj.counit_com f
   , natural := sorry
   }

/-! #brief Cone used to define the component of the unit of the BaseChangeFun/LeanCat.DepProdFun adjunction.
-/
definition LeanCat.BaseChange_DepProd.Adj.unit_com.cone
    {x y : LeanCat.{ℓ}^.obj}
    (f : LeanCat.{ℓ}^.hom x y)
    [f_HasPullbacksAlong : HasPullbacksAlong LeanCat.{ℓ} f]
    (Y : OverObj LeanCat.{ℓ} y)
    (Yy : OverObj.dom Y)
    (Xx : {b // f b = Y^.hom Yy})
    : PullbackCone LeanCat.{ℓ} (f ↗→ Y^.hom ↗→↗)
:= sorry
-- := @PullbackCone.mk LeanCat.{ℓ} _ _ _
--     (f ↗→ Y^.hom ↗→↗) {b // f b = Y^.hom Yy}
--     (λ Xx, f Xx^.val) (subtype.val ↗← (λ Xx, Yy) ↗←↗)
--     begin
--       apply dlist.eq,
--       { trivial },
--       apply dlist.eq,
--       { apply funext, intro Xx, cases Xx with Xx ωXx,
--         exact sorry
--       }
--       , trivial
--     end

/-! #brief Component of the unit of the BaseChangeFun/LeanCat.DepProdFun adjunction.
-/
definition LeanCat.BaseChange_DepProd.Adj.unit_com
    {x y : LeanCat.{ℓ}^.obj}
    (f : LeanCat.{ℓ}^.hom x y)
    [f_HasPullbacksAlong : HasPullbacksAlong LeanCat.{ℓ} f]
    (Y : OverObj LeanCat.{ℓ} y)
    : OverHom LeanCat.{ℓ} y
        Y
        (LeanCat.DepProdFun.obj f (BaseChangeFun.obj f Y))
:= sorry
-- := { hom := λ Yy, { fst := Y^.hom Yy
--                   , snd := λ Xx
--                            , { val := pullback.univ LeanCat.{ℓ}
--                                        (f ↗→ Y^.hom ↗→↗)
--                                        (LeanCat.BaseChange_DepProd.Adj.unit_com.cone f Y Yy Xx) Xx
--                              , property := sorry
--                              }
--                   }
--    , triangle := sorry
--    }

/-! #brief Unit of the BaseChangeFun/LeanCat.DepProdFun adjunction.
-/
definition LeanCat.BaseChange_DepProd.Adj.unit
    {x y : LeanCat.{ℓ}^.obj}
    (f : LeanCat.{ℓ}^.hom x y)
    [f_HasPullbacksAlong : HasPullbacksAlong LeanCat.{ℓ} f]
    : NatTrans (Fun.id (OverCat LeanCat.{ℓ} y))
               (LeanCat.DepProdFun f □□ @BaseChangeFun LeanCat.{ℓ} x y f f_HasPullbacksAlong)
:= { com := LeanCat.BaseChange_DepProd.Adj.unit_com f
   , natural := sorry
   }


/-! #brief Left-identity of the BaseChangeFun/LeanCat.DepProdFun adjunction.
-/
theorem LeanCat.BaseChange_DepProd.Adj.id_left
    {x y : LeanCat.{ℓ}^.obj}
    (f : LeanCat.{ℓ}^.hom x y)
    [f_HasPullbacksAlong : HasPullbacksAlong LeanCat.{ℓ} f]
    (Y : OverObj LeanCat.{ℓ} y)
    : OverHom.comp LeanCat x _ _ _
        (LeanCat.BaseChange_DepProd.Adj.counit_com f (BaseChangeFun.obj f Y))
        (BaseChangeFun.hom f _ _ (LeanCat.BaseChange_DepProd.Adj.unit_com f Y))
       = OverHom.id LeanCat x (BaseChangeFun.obj f Y)
:= sorry

/-! #brief Right-identity of the BaseChangeFun/LeanCat.DepProdFun adjunction.
-/
theorem LeanCat.BaseChange_DepProd.Adj.id_right
    {x y : LeanCat.{ℓ}^.obj}
    (f : LeanCat.{ℓ}^.hom x y)
    [f_HasPullbacksAlong : HasPullbacksAlong LeanCat.{ℓ} f]
    (X : OverObj LeanCat.{ℓ} x)
    : OverHom.comp LeanCat y _ _ _
        (LeanCat.DepProdFun.hom f (LeanCat.BaseChange_DepProd.Adj.counit_com f X))
        (LeanCat.BaseChange_DepProd.Adj.unit_com f (LeanCat.DepProdFun.obj f X))
       = OverHom.id LeanCat y (LeanCat.DepProdFun.obj f X)
:= sorry


/-! #brief BaseChangeFun and LeanCat.DepProdFun are adjoint.
-/
definition LeanCat.BaseChange_DepProd.Adj
    {x y : LeanCat.{ℓ}^.obj}
    (f : LeanCat.{ℓ}^.hom x y)
    [f_HasPullbacksAlong : HasPullbacksAlong LeanCat.{ℓ} f]
    : Adj (@BaseChangeFun LeanCat.{ℓ} x y f f_HasPullbacksAlong)
          (LeanCat.DepProdFun f)
:= { counit := LeanCat.BaseChange_DepProd.Adj.counit f
   , unit := LeanCat.BaseChange_DepProd.Adj.unit f
   , id_left := LeanCat.BaseChange_DepProd.Adj.id_left f
   , id_right := LeanCat.BaseChange_DepProd.Adj.id_right f
   }


/-! #brief LeanCat has dependent product.
-/
instance LeanCat.HasDepProd
    : HasDepProd LeanCat.{ℓ}
:= { depprod := λ x y f f_HasPullbacksAlong, @LeanCat.DepProdFun x y f
   , adj := @LeanCat.BaseChange_DepProd.Adj
   }



/- -----------------------------------------------------------------------
Existence of W-types in LeanCat.
----------------------------------------------------------------------- -/

definition fancyquot
    {B A : LeanCat.{ℓ}^.obj}
    (disp : LeanCat.{ℓ}^.hom B A)
    (L : Fun NatCat (OverCat LeanCat.{ℓ} B))
    (a : A)
    (fibers : list {b : B // disp b = a})
:= quot (λ (X Y : Σ n, ListProd (list.map (λ (b : {b : B // disp b = a})
                                           , {x : (L^.obj n)^.obj // (L^.obj n)^.hom x = b^.val})
                                          fibers))
         , ∃ (f : NatCat^.hom X^.fst Y^.fst)
           , ListProd.map (λ (b : {b // disp b = a})
                             (y : {x // (L^.obj (Y^.fst))^.hom x = b^.val})
                           , y^.val)
              fibers Y^.snd
             = ListProd.map (λ (b : {b // disp b = a})
                               (x : {x // (L^.obj (X^.fst))^.hom x = b^.val})
                             , (L^.hom f)^.hom x^.val)
                fibers X^.snd)

definition LeanCat.DepProdFun.PresCoLimit.hom''
    {B A : LeanCat.{ℓ}^.obj}
    (disp : LeanCat.{ℓ}^.hom B A)
    (L : Fun NatCat (OverCat LeanCat.{ℓ} B))
    (a : A)
    : ∀ (fibers : list {b : B // disp b = a})
      , ListProd (list.map (λ (b : {b : B // disp b = a})
                            , {x : (colimit L)^.obj // (colimit L)^.hom x = b^.val})
                           fibers)
      → fancyquot disp L a fibers
| [] u := quot.mk _ { fst := nat.zero
                    , snd := punit.star
                    }
| [Ba] (subtype.mk b ωb)
:= let h : (Σ (n : ℕ), (L^.obj n)^.obj)
           → fancyquot disp L a [Ba]
        := λ l, quot.mk _ { fst := l^.fst
                          , snd := { val := l^.snd
                                   , property := sorry
                                   }
                          }
in quot.lift h
    begin
      intros l₁ l₂ ωl,
      apply quot.sound,
      exact ωl
    end
    b
| (Ba :: Ba₀ :: BB) (prod.mk b bb)
:= let h₁ : (Σ (n : ℕ), (L^.obj n)^.obj)
           → (Σ n, ListProd (list.map (λ (b : {b : B // disp b = a})
                                      , {x : (L^.obj n)^.obj // (L^.obj n)^.hom x = b^.val})
                                     (Ba₀ :: BB)))
           → fancyquot disp L a (Ba :: Ba₀ :: BB)
         := λ x₁ x₂, quot.mk _
                     { fst := nat.max x₁^.fst x₂^.fst
                     , snd := ( { val := (L^.hom (nat.le_max_left _ _))^.hom x₁^.snd
                                , property := sorry
                                }
                              , ListProd.map
                                  (λ (b : {b // disp b = a})
                                     (x : {x // (L^.obj (x₂^.fst))^.hom x = b^.val})
                                   , @subtype.mk
                                      (L^.obj (nat.max (x₁^.fst) (x₂^.fst)))^.obj
                                      (λ x, (L^.obj (nat.max (x₁^.fst) (x₂^.fst)))^.hom x = b^.val)
                                      ((L^.hom (nat.le_max_right x₁^.fst x₂^.fst))^.hom x^.val)
                                      sorry)
                                  (Ba₀ :: BB) x₂^.snd)
                     }
in let h₂ : (Σ (n : ℕ), (L^.obj n)^.obj)
           → fancyquot disp L a (Ba₀ :: BB)
           → fancyquot disp L a (Ba :: Ba₀ :: BB)
        := λ x₁, quot.lift (h₁ x₁)
                  begin
                    intros l₁ l₂ ωl,
                    apply quot.sound,
                    dsimp,
                    exact sorry
                  end
in quot.lift h₂
    begin
      intros l₁ l₂ ωl,
      apply funext, intro x₁,
      dsimp,
      exact sorry
    end
    b^.val
    (LeanCat.DepProdFun.PresCoLimit.hom'' (Ba₀ :: BB) bb)

definition LeanCat.DepProdFun.PresCoLimit.hom'
    {B A : LeanCat.{ℓ}^.obj}
    (disp : LeanCat.{ℓ}^.hom B A)
    (L : Fun NatCat (OverCat LeanCat.{ℓ} B))
    (a : A)
    [a_FinFiber : FinType {b : B // disp b = a}]
    : @product LeanCat {b : B // disp b = a}
        (λ b, { x : (colimit L)^.obj // (colimit L)^.hom x = b^.val})
        (LeanCat.HasProduct.{ℓ ℓ} _)
      → (colimit (OverFun.out LeanCat A □□ (LeanCat.DepProdFun disp □□ L)))
      -- → quot (LeanCat.HasAllCoLimits.prop.{ℓ 0 0}
      --           (OverFun.out LeanCat A □□ (LeanCat.DepProdFun disp □□ L)))
      -- → quot (λ (X Y : Σ n, @coproduct LeanCat A
      --                         (λ a, @product LeanCat {b : B // disp b = a}
      --                                 (λ (b : {b // disp b = a}), {x // (L^.obj n)^.hom x = b^.val})
      --                                 (LeanCat.HasProduct.{ℓ ℓ} _))
      --                         (LeanCat.HasCoProduct.{ℓ ℓ} _))
      --         , ∃ (f : NatCat^.hom X^.fst Y^.fst), Y^.snd = (LeanCat.DepProdFun.hom disp (L^.hom f))^.hom X^.snd)
:= λ ll, --quot.mk _ { fst := begin end, snd := { fst := a, snd := λ b, begin end } }
begin
exact sorry
end

definition LeanCat.DepProdFun.PresCoLimit.hom
    {B A : LeanCat.{ℓ}^.obj}
    (disp : LeanCat.{ℓ}^.hom B A)
    (ωdisp : ∀ (a : A), FinType { b : B // disp b = a })
    (L : Fun NatCat (OverCat LeanCat.{ℓ} B))
    : OverHom LeanCat A
        ((LeanCat.DepProdFun disp)^.obj (colimit L))
        (colimit (LeanCat.DepProdFun disp □□ L))
:= { hom := λ af, LeanCat.DepProdFun.PresCoLimit.hom' disp L af^.fst af^.snd
   , triangle
      := begin
           apply funext, intro af,
           cases af with a f,
           exact sorry
         end
   }

/-! #brief LeanCat.DepProdFun on a map with finite fibers preserves NatCat-colimits.
-/
definition LeanCat.DepProdFun.PresCoLimit
    {B A : LeanCat.{ℓ}^.obj}
    (disp : LeanCat.{ℓ}^.hom B A)
    (ωdisp : ∀ (a : A), FinType { b : B // disp b = a })
    (L : Fun NatCat (OverCat LeanCat.{ℓ} B))
    : PresCoLimit L (LeanCat.DepProdFun disp)
:= PresCoLimit.show
    (λ L_HasCoLimit C hom ωhom
     , let ccone : CoCone (LeanCat.DepProdFun disp □□ L)
                := CoCone.mk C hom @ωhom
       in (OverCat LeanCat A)^.circ
           ((OverCat LeanCat A)^.circ
              (@colimit.univ _ _ _ (LeanCat.Over.HasCoLimit _ _) ccone)
              (LeanCat.DepProdFun.PresCoLimit.hom disp ωdisp L))
           ((LeanCat.DepProdFun disp)^.hom (colimit.iso L_HasCoLimit (LeanCat.Over.HasCoLimit B L))))
    sorry
    sorry


definition LeanCat.HasWType {B A : LeanCat.{ℓ}^.obj}
    (disp : LeanCat.{ℓ}^.hom B A)
    (ωdisp : ∀ (a : A), FinType { b : B // disp b = a })
    : @HasWType LeanCat
        LeanCat.HasFinal
        LeanCat.HasDepProd
        LeanCat.HasAllPullbacks
        B A disp
:= @HasWType.Adamek LeanCat.{ℓ}
    LeanCat.HasInit
    LeanCat.HasFinal
    LeanCat.HasDepProd
    LeanCat.HasAllPullbacks
    (HasAllCoLimits.HasAllCoLimitsFrom LeanCat.{ℓ} NatCat)
    B A disp
    ({ pres_colimit := LeanCat.DepProdFun.PresCoLimit disp ωdisp })

end qp
