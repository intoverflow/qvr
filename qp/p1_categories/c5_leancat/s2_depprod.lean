/- -----------------------------------------------------------------------
Dependent products in LeanCat.
----------------------------------------------------------------------- -/

import ..c1_basic
import ..c2_limits
import ..c3_wtypes

namespace qp

open stdaux

universe variables ℓ


/- -----------------------------------------------------------------------
The dependent product functor.
----------------------------------------------------------------------- -/

/-! #brief The dependent product functor on objects.
-/
definition LeanCat.DepProdFun.obj {B A : LeanCat.{ℓ}^.obj}
    (disp : LeanCat.{ℓ}^.hom B A)
    (S : OverObj LeanCat.{ℓ} B)
    : OverObj LeanCat.{ℓ} A
:= { obj := Σ (a : A)
            , ∀ (b : {b : B // disp b = a})
              , { x : S^.obj // S^.hom x = b^.val}
   , hom := sigma.fst
   }

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



/- -----------------------------------------------------------------------
The dependent product functor is right adjoint to base change.
----------------------------------------------------------------------- -/

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
:= { hom := let pb₀ := pullback.π LeanCat.{ℓ} (f ↗→ (LeanCat.DepProdFun.obj f X)^.hom ↗→↗) (@fin_of 1 0)
         in let pb₁ := pullback.π LeanCat.{ℓ} (f ↗→ (LeanCat.DepProdFun.obj f X)^.hom ↗→↗) (@fin_of 0 1)
            in λ Z, ((pb₁ Z)^.snd { val := pb₀ Z, property := sorry })^.val
   , triangle := sorry
   }

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
:= @PullbackCone.mk LeanCat.{ℓ} _ _ _
    (f ↗→ Y^.hom ↗→↗) {b // f b = Y^.hom Yy}
    (λ Xx, f Xx^.val) (subtype.val ↗← (λ Xx, Yy) ↗←↗)
    begin
      apply dlist.eq,
      { trivial },
      apply dlist.eq,
      { apply funext, intro Xx, cases Xx with Xx ωXx,
        exact sorry
      }
      , trivial
    end

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
:= { hom := λ Yy, { fst := Y^.hom Yy
                  , snd := λ Xx
                           , { val := pullback.univ LeanCat.{ℓ}
                                       (f ↗→ Y^.hom ↗→↗)
                                       (LeanCat.BaseChange_DepProd.Adj.unit_com.cone f Y Yy Xx) Xx
                             , property := sorry
                             }
                  }
   , triangle := sorry
   }

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
instance LeanCat.HasDepProdFun
    : HasDepProdFun LeanCat.{ℓ}
:= { depprod := @LeanCat.DepProdFun
   , adj := @LeanCat.BaseChange_DepProd.Adj
   }

end qp
