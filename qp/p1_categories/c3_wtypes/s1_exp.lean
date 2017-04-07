/- -----------------------------------------------------------------------
Exponential obejcts.
----------------------------------------------------------------------- -/

import ..c1_basic
import ..c2_limits

namespace qp

open stdaux

universe variables ℓobj ℓhom

/-! #brief An exponential object.
-/
class HasExp (C : Cat.{ℓobj ℓhom})
    (X Y : C^.obj)
:= (exp : C^.obj)
   (ev
     : ∀ [exp_Y_HasFinProduct : HasFinProduct C [exp, Y]]
       , C^.hom (finproduct C [exp, Y]) X)
   (univ
     : ∀ (Z : C^.obj) [Z_Y_HasFinProduct : HasFinProduct C [Z, Y]]
         (e : C^.hom (finproduct C [Z, Y]) X)
       , C^.hom Z exp)
   (factor
     : ∀ [exp_Y_HasFinProduct : HasFinProduct C [exp, Y]]
         (Z : C^.obj) [Z_Y_HasFinProduct : HasFinProduct C [Z, Y]]
         (e : C^.hom (finproduct C [Z, Y]) X)
       , e = ev ∘∘ finproduct.hom (univ Z e ↗ C^.id Y ↗↗))
   (uniq
     : ∀ [exp_Y_HasFinProduct : HasFinProduct C [exp, Y]]
         (Z : C^.obj) [Z_Y_HasFinProduct : HasFinProduct C [Z, Y]]
         (e : C^.hom (finproduct C [Z, Y]) X)
         (u : C^.hom Z exp)
         (ωu : e = ev ∘∘ finproduct.hom (u ↗ C^.id Y ↗↗))
       , u = univ Z e)

/-! #brief A category with all exponential obejcts.
-/
class HasAllExp (C : Cat.{ℓobj ℓhom})
:= (has_exp : ∀ (X Y : C^.obj), HasExp C X Y)

instance HasAllExp.HasExp {C : Cat.{ℓobj ℓhom}}
    [C_HasAllExp : HasAllExp C]
    (X Y : C^.obj)
    : HasExp C X Y
:= HasAllExp.has_exp X Y

/-! #brief A category which locally has all exponential obejcts.
-/
class HasAllLocalExp (C : Cat.{ℓobj ℓhom})
:= (has_exp : ∀ (A : C^.obj) (X Y : (OverCat C A)^.obj)
              , HasExp (OverCat C A) X Y)

instance HasAllLocalExp.HasAllExp (C : Cat.{ℓobj ℓhom})
    [C_HasAllLocalExp : HasAllLocalExp C]
    (A : C^.obj)
    : HasAllExp (OverCat C A)
:= { has_exp := HasAllLocalExp.has_exp A
   }

/-! #brief An exponential object.
-/
definition expon (C : Cat.{ℓobj ℓhom})
    (X Y : C^.obj)
    [X_Y_HasExp : HasExp C X Y]
    : C^.obj
:= HasExp.exp X Y

/-! #brief An evaluation map.
-/
definition expon.eval (C : Cat.{ℓobj ℓhom})
    (X Y : C^.obj)
    [X_Y_HasExp : HasExp C X Y]
    [exp_Y_HasFinProduct : HasFinProduct C [expon C X Y, Y]]
    : C^.hom (finproduct C [expon C X Y, Y]) X
:= HasExp.ev X Y

/-! #brief A universal map.
-/
definition expon.univ (C : Cat.{ℓobj ℓhom})
    {X Y : C^.obj}
    [X_Y_HasExp : HasExp C X Y]
    {Z : C^.obj}
    [Z_Y_HasFinProduct : HasFinProduct C [Z, Y]]
    (e : C^.hom (finproduct C [Z, Y]) X)
    : C^.hom Z (expon C X Y)
:= HasExp.univ Z e

/-! #brief The universal map factors.
-/
theorem expon.univ.factor {C : Cat.{ℓobj ℓhom}}
    {X Y : C^.obj}
    [X_Y_HasExp : HasExp C X Y]
    [exp_Y_HasFinProduct : HasFinProduct C [expon C X Y, Y]]
    {Z : C^.obj}
    [Z_Y_HasFinProduct : HasFinProduct C [Z, Y]]
    {e : C^.hom (finproduct C [Z, Y]) X}
    : e = expon.eval C X Y ∘∘ finproduct.hom (expon.univ C e ↗ C^.id Y ↗↗)
:= HasExp.factor Z e

/-! #brief The universal map is unique.
-/
theorem expon.univ.uniq {C : Cat.{ℓobj ℓhom}}
    {X Y : C^.obj}
    [X_Y_HasExp : HasExp C X Y]
    [exp_Y_HasFinProduct : HasFinProduct C [expon C X Y, Y]]
    {Z : C^.obj} [Z_Y_HasFinProduct : HasFinProduct C [Z, Y]]
    (e : C^.hom (finproduct C [Z, Y]) X)
    (u : C^.hom Z (expon C X Y))
    (ωu : e = expon.eval C X Y ∘∘ finproduct.hom (u ↗ C^.id Y ↗↗))
    : u = expon.univ C e
:= @HasExp.uniq C X Y X_Y_HasExp exp_Y_HasFinProduct Z Z_Y_HasFinProduct e u ωu

/-! #brief The universal map induced by eval is the identity.
-/
theorem expon.univ_eval {C : Cat.{ℓobj ℓhom}}
    {X Y : C^.obj}
    [X_Y_HasExp : HasExp C X Y]
    [exp_Y_HasFinProduct : HasFinProduct C [expon C X Y, Y]]
    : C^.id (expon C X Y) = expon.univ C (expon.eval C X Y)
:= expon.univ.uniq _ _ begin exact sorry end



/- -----------------------------------------------------------------------
Homs induce maps between exponentials.
----------------------------------------------------------------------- -/

/-! #brief Hom induced by composition on the right.
-/
definition expon.circ_right {C : Cat.{ℓobj ℓhom}}
    {Z X Y : C^.obj}
    [Z_X_HasExp : HasExp C Z X]
    [Z_Y_HasExp : HasExp C Z Y]
    [exp_Y_HasFinProduct : HasFinProduct C [expon C Z Y, Y]]
    [exp_X_HasFinProduct : HasFinProduct C [expon C Z Y, X]]
    (f : C^.hom X Y)
    : C^.hom (expon C Z Y) (expon C Z X)
:= expon.univ C (C^.circ (expon.eval C Z Y) (finproduct.hom (C^.id (expon C Z Y) ↗ f ↗↗)))

/-! #brief Hom induced by composition on the left.
-/
definition expon.circ_left {C : Cat.{ℓobj ℓhom}}
    {X Y Z : C^.obj}
    [X_Z_HasExp : HasExp C X Z]
    [Y_Z_HasExp : HasExp C Y Z]
    [exp_Z_HasFinProduct : HasFinProduct C [expon C X Z, Z]]
    (g : C^.hom X Y)
    : C^.hom (expon C X Z) (expon C Y Z)
:= expon.univ C (C^.circ g (expon.eval C X Z))

/-! #brief Exponential objects are unique up-to unique isomorphism.
-/
definition expon.iso₁ {C : Cat.{ℓobj ℓhom}}
    {X Y : C^.obj}
    (X_Y_HasExp₁ X_Y_HasExp₂ : HasExp C X Y)
    [exp_Y_HasFinProduct₁ : HasFinProduct C [@expon C X Y X_Y_HasExp₁, Y]]
    : C^.hom (@expon C X Y X_Y_HasExp₁) (@expon C X Y X_Y_HasExp₂)
:= @expon.circ_left C X X Y X_Y_HasExp₁ X_Y_HasExp₂ exp_Y_HasFinProduct₁ (C^.id X)

/-! #brief Exponential objects are unique up-to unique isomorphism.
-/
definition expon.iso₂ {C : Cat.{ℓobj ℓhom}}
    {X Y : C^.obj}
    (X_Y_HasExp₁ X_Y_HasExp₂ : HasExp C X Y)
    [exp_Y_HasFinProduct₂ : HasFinProduct C [@expon C X Y X_Y_HasExp₂, Y]]
    : C^.hom (@expon C X Y X_Y_HasExp₂) (@expon C X Y X_Y_HasExp₁)
:= @expon.circ_left C X X Y X_Y_HasExp₂ X_Y_HasExp₁ exp_Y_HasFinProduct₂ (C^.id X)

/-! #brief Exponential objects are unique up-to unique isomorphism.
-/
definition expon.iso {C : Cat.{ℓobj ℓhom}}
    {X Y : C^.obj}
    (X_Y_HasExp₁ X_Y_HasExp₂ : HasExp C X Y)
    [exp_Y_HasFinProduct₁ : HasFinProduct C [@expon C X Y X_Y_HasExp₁, Y]]
    [exp_Y_HasFinProduct₂ : HasFinProduct C [@expon C X Y X_Y_HasExp₂, Y]]
    : Iso (expon.iso₁ X_Y_HasExp₁ X_Y_HasExp₂)
          (expon.iso₂ X_Y_HasExp₁ X_Y_HasExp₂)
:= sorry



/- -----------------------------------------------------------------------
The exponential functor.
----------------------------------------------------------------------- -/

/-! #brief The exponential functor.
-/
definition ExpFun (C : Cat.{ℓobj ℓhom})
    [C_HasAllExp : HasAllExp C]
    [C_HasAllFinProducts : HasAllFinProducts C]
    (W : C^.obj)
    : Fun C C
:= { obj := λ X, expon C X W
   , hom := λ X Y f, expon.circ_left f
   , hom_id := λ X
               , begin
                   dsimp [expon.circ_left],
                   rw C^.circ_id_left,
                   apply eq.symm expon.univ_eval
                 end
   , hom_circ
      := λ X Y Z g f
         , begin
             dsimp [expon.circ_left],
             refine eq.symm (expon.univ.uniq _ _ _),
             refine eq.trans _
                     (Cat.circ.congr_right
                       (eq.trans 
                         (eq.symm (finproduct.hom₂.circ
                                    (expon.univ C (g ∘∘ expon.eval C Y W)) ⟨⟨W⟩⟩
                                    (expon.univ C (f ∘∘ expon.eval C X W)) ⟨⟨W⟩⟩))
                         (by rw C^.circ_id_right))),
             refine eq.trans _ (eq.symm C^.circ_assoc),
             refine eq.trans _ (Cat.circ.congr_left expon.univ.factor),
             refine eq.trans (eq.symm C^.circ_assoc)
                (eq.trans (Cat.circ.congr_right expon.univ.factor) C^.circ_assoc),
           end
   }



/- -----------------------------------------------------------------------
The dependent product functor.
----------------------------------------------------------------------- -/

/-! #brief The dependent product functor.
-/
definition HasAllExp.DepProdFun (C : Cat.{ℓobj ℓhom})
    {B A : C^.obj} (f : C^.hom B A)
    [C_HasAllExp : HasAllExp (OverCat C A)]
    [C_HasAllFinProducts : HasAllFinProducts (OverCat C A)]
    : Fun (OverCat C B) (OverCat C A)
:= let f_obj : (OverCat C A)^.obj
            := { obj := B, hom := f }
in let codom_obj : (OverCat C B)^.obj → (OverCat C A)^.obj
                := λ Q, { obj := Q^.obj
                        , hom := C^.circ f Q^.hom
                        }
   in { obj := λ Q, (ExpFun (OverCat C A) f_obj)^.obj (codom_obj Q)
   , hom := λ Q₁ Q₂ h, (ExpFun (OverCat C A) f_obj)^.hom
                        { hom := h^.hom
                        , triangle
                           := begin
                                dsimp [OverObj.down],
                                rw -C^.circ_assoc,
                                exact Cat.circ.congr_right h^.triangle
                              end
                        }
   , hom_id
      := λ Q
         , eq.trans (congr_arg _ (OverHom.eq begin trivial end))
                    (ExpFun (OverCat C A) f_obj)^.hom_id
   , hom_circ
      := λ Q₁ Q₂ Q₃ h g
         , eq.trans (congr_arg _ (OverHom.eq begin trivial end))
                    (ExpFun (OverCat C A) f_obj)^.hom_circ
   }



/-! #brief Counit of the adjunction between base change and dependent product.
-/
definition HasAllExp.BaseChange_DepProd.Adj.counit.com {C : Cat.{ℓobj ℓhom}}
    {B A : C^.obj} (f : C^.hom B A)
    [f_HasPullbacksAlong : HasPullbacksAlong C f]
    [C_HasAllExp : HasAllExp (OverCat C A)]
    [C_A_HasAllFinProducts : HasAllFinProducts (OverCat C A)]
    : ∀ (Q : OverObj C B)
      , OverHom C B
          ((BaseChangeFun f □□ HasAllExp.DepProdFun C f)^.obj Q)
          Q
| (OverObj.mk Q h)
:= { hom := (expon.eval (OverCat C A) (OverObj.mk Q (f ∘∘ h)) (OverObj.mk B f))^.hom
             ∘∘ sorry
   , triangle := sorry
   }

/-! #brief Counit of the adjunction between base change and dependent product.
-/
definition HasAllExp.BaseChange_DepProd.Adj.counit {C : Cat.{ℓobj ℓhom}}
    {B A : C^.obj} (f : C^.hom B A)
    [f_HasPullbacksAlong : HasPullbacksAlong C f]
    [C_HasAllExp : HasAllExp (OverCat C A)]
    [C_HasAllFinProducts : HasAllFinProducts (OverCat C A)]
    : NatTrans (BaseChangeFun f □□ HasAllExp.DepProdFun C f)
               (Fun.id (OverCat C B))
:= { com := HasAllExp.BaseChange_DepProd.Adj.counit.com f
   , natural := sorry
   }


/-! #brief Unit of the adjunction between base change and dependent product.
-/
definition HasAllExp.BaseChange_DepProd.Adj.unit.com {C : Cat.{ℓobj ℓhom}}
    {B A : C^.obj} (f : C^.hom B A)
    [f_HasPullbacksAlong : HasPullbacksAlong C f]
    [C_HasAllExp : HasAllExp (OverCat C A)]
    [C_HasAllFinProducts : HasAllFinProducts (OverCat C A)]
    (Q : OverObj C A)
    : OverHom C A
        Q
        ((HasAllExp.DepProdFun C f □□ BaseChangeFun f)^.obj Q)
:= { hom := sorry
   , triangle := sorry
   }

/-! #brief Unit of the adjunction between base change and dependent product.
-/
definition HasAllExp.BaseChange_DepProd.Adj.unit {C : Cat.{ℓobj ℓhom}}
    {B A : C^.obj} (f : C^.hom B A)
    [f_HasPullbacksAlong : HasPullbacksAlong C f]
    [C_HasAllExp : HasAllExp (OverCat C A)]
    [C_HasAllFinProducts : HasAllFinProducts (OverCat C A)]
    : NatTrans (Fun.id (OverCat C A))
               (HasAllExp.DepProdFun C f □□ BaseChangeFun f)
:= { com := HasAllExp.BaseChange_DepProd.Adj.unit.com f
   , natural := sorry
   }


/-! #brief Base change is adjoint to dependent product.
-/
definition HasAllExp.BaseChange_DepProd.Adj (C : Cat.{ℓobj ℓhom})
    {B A : C^.obj} (f : C^.hom B A)
    [f_HasPullbacksAlong : HasPullbacksAlong C f]
    [C_HasAllExp : HasAllExp (OverCat C A)]
    [C_HasAllFinProducts : HasAllFinProducts (OverCat C A)]
    : Adj (BaseChangeFun f) (HasAllExp.DepProdFun C f)
:= { counit := HasAllExp.BaseChange_DepProd.Adj.counit f
   , unit := HasAllExp.BaseChange_DepProd.Adj.unit f
   , id_left := sorry
   , id_right := sorry
   }


-- /-! #brief Locally cartesian closed categories have dependent product.
-- -/
-- instance HasAllExp.HasDepProdFun (C : Cat.{ℓobj ℓhom})
--     [C_HasAllLocalExp : HasAllLocalExp C]
--     [C_HasAllPullbacks : HasAllPullbacks C]
--     : HasDepProdFun C
-- := { depprod := λ x y f, HasAllExp.DepProdFun C f
--    , adj := λ x y f f_HasPullbacksAlong, begin end -- HasAllExp.BaseChange_DepProd.Adj C f
--    }


end qp
