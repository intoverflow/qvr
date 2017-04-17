/- -----------------------------------------------------------------------
Base change, dependent sum, and dependent product.
----------------------------------------------------------------------- -/

import ..c2_limits

namespace qp

open stdaux

universe variables ℓobj ℓhom

/- -----------------------------------------------------------------------
Base change.
----------------------------------------------------------------------- -/

/-! #brief Action of base change on objects.
-/
definition BaseChangeFun.obj {C : Cat.{ℓobj ℓhom}}
    {x y : C^.obj}
    (f : C^.hom x y)
    [f_HasPullbacksAlong : HasPullbacksAlong C f]
    (Y : OverObj C y)
    : OverObj C x
:= { obj := pullback C (f ↗→ Y^.hom ↗→↗)
   , hom := pullback.π C (f ↗→ Y^.hom ↗→↗) (@fin_of 1 0)
   }

/-! #brief Action of base change on homs.
-/
definition BaseChangeFun.hom {C : Cat.{ℓobj ℓhom}}
    {x y : C^.obj}
    (f : C^.hom x y)
    [f_HasPullbacksAlong : HasPullbacksAlong C f]
    (Y₁ Y₂ : OverObj C y) (h : OverHom C y Y₁ Y₂)
    : OverHom C x (BaseChangeFun.obj f Y₁) (BaseChangeFun.obj f Y₂)
:= { hom := pullback.hom C
             (x, x) [(Y₁^.obj, Y₂^.obj)]
             (f ↗→ Y₁^.hom ↗→↗)
             (f ↗→ Y₂^.hom ↗→↗)
             (C^.id x ↗ h^.hom ↗↗)
   , triangle := sorry
   }

/-! #brief A base change functor.
-/
definition BaseChangeFun {C : Cat.{ℓobj ℓhom}}
    {x y : C^.obj}
    (f : C^.hom x y)
    [f_HasPullbacksAlong : HasPullbacksAlong C f]
    : Fun (OverCat C y) (OverCat C x)
:= { obj := BaseChangeFun.obj f
   , hom := BaseChangeFun.hom f
   , hom_id := λ Y, OverHom.eq sorry
   , hom_circ := λ X Y Z G F, OverHom.eq sorry
   }



/- -----------------------------------------------------------------------
Dependent sum.
----------------------------------------------------------------------- -/

/-! #brief The dependent sum functor.
-/
definition DepSumFun {C : Cat.{ℓobj ℓhom}}
    {x y : C^.obj}
    (f : C^.hom x y)
    : Fun (OverCat C x) (OverCat C y)
:= { obj := λ X
            , { obj := X^.obj
              , hom := C^.circ f X^.hom
              }
   , hom := λ X Y F
            , { hom := F^.hom
              , triangle
                 := begin
                      rw -C^.circ_assoc,
                      exact Cat.circ.congr_right  F^.triangle
                    end
              }
   , hom_id := λ X, rfl
   , hom_circ := λ X Y Z G F, rfl
   }

/-! #brief A hom into a dependent sum object.
-/
definition DepSumFun.into {C : Cat.{ℓobj ℓhom}}
    {x y : C^.obj} (f : C^.hom x y)
    (X : OverObj C y)
    (Y : OverObj C x)
    (Xx : C^.hom X^.obj x)
    (ωXx : X^.hom = f ∘∘ Xx)
    (h : (OverCat C x)^.hom
           { obj := X^.obj
           , hom := Xx
           }
           Y)
    : (OverCat C y)^.hom X ((DepSumFun f)^.obj Y)
:= { hom := h^.hom
   , triangle := by calc X^.hom = f ∘∘ Xx                 : ωXx
                         ...    = f ∘∘ (Y^.hom ∘∘ h^.hom) : Cat.circ.congr_right h^.triangle
                         ...    = f ∘∘ Y^.hom ∘∘ h^.hom   : C^.circ_assoc
   }

/-! #brief Dependent sum is adjoint to base change.
-/
definition DepSum_BaseChange.Adj {C : Cat.{ℓobj ℓhom}}
    {x y : C^.obj}
    (f : C^.hom x y)
    [f_HasPullbacksAlong : HasPullbacksAlong C f]
    : Adj (DepSumFun f) (BaseChangeFun f)
:= { counit
      := { com := λ Y, { hom := pullback.π C (f ↗→ Y^.hom ↗→↗) (@fin_of 0 1)
                       , triangle := sorry
                       }
         , natural := sorry
         }
   , unit
      := { com := λ X, { hom := pullback.univ C (f ↗→ (f ∘∘ X^.hom) ↗→↗)
                                  (PullbackCone.mk (f ↗→ (f ∘∘ X^.hom) ↗→↗)
                                    X^.dom
                                    (f ∘∘ X^.hom)
                                    (X^.hom ↗← ⟨⟨ X^.obj ⟩⟩ ↗←↗)
                                    begin
                                      apply dlist.eq,
                                      { trivial },
                                      apply dlist.eq,
                                      { rw [-C^.circ_assoc, C^.circ_id_right] },
                                      trivial
                                    end)
                       , triangle := sorry
                       }
         , natural := sorry
         }
   , id_left
      := λ c
         , OverHom.eq
            begin
              dsimp [OverCat, OverHom.id, OverHom.comp, DepSumFun],
              exact sorry
            end
   , id_right
      := λ c
         , OverHom.eq
            begin
              exact sorry
            end
   }



/- -----------------------------------------------------------------------
Dependent product.
----------------------------------------------------------------------- -/

/-! #brief A category with dependent products.
-/
class HasDepProd (C : Cat.{ℓobj ℓhom})
:= (depprod
     : ∀ {x y : C^.obj} (f : C^.hom x y)
         [f_HasPullbacksAlong : HasPullbacksAlong C f]
       , Fun (OverCat C x) (OverCat C y))
   (adj
     : ∀ {x y : C^.obj} (f : C^.hom x y)
         [f_HasPullbacksAlong : HasPullbacksAlong C f]
       , Adj (BaseChangeFun f) (depprod f))

/-! #brief A dependent product functor.
-/
definition DepProdFun {C : Cat.{ℓobj ℓhom}}
    [C_HasDepProd : HasDepProd C]
    {x y : C^.obj}
    (f : C^.hom x y)
    [f_HasPullbacksAlong : HasPullbacksAlong C f]
    : Fun (OverCat C x) (OverCat C y)
:= HasDepProd.depprod f

/-! #brief Base change is adjoint to dependent product.
-/
definition BaseChange_DepProd.Adj {C : Cat.{ℓobj ℓhom}}
    [C_HasDepProd : HasDepProd C]
    {x y : C^.obj}
    (f : C^.hom x y)
    [f_HasPullbacksAlong : HasPullbacksAlong C f]
    : Adj (BaseChangeFun f) (DepProdFun f)
:= HasDepProd.adj f

end qp
