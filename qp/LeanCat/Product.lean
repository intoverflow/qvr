/- ----------------------------------------------------------------------------
Products in LeanCat.
---------------------------------------------------------------------------- -/

import ..Cat
import .Limit

namespace qp
universe variables ℓ



/- ----------------------------------------------------------------------------
Products.
---------------------------------------------------------------------------- -/

/-! #brief The Lean categories have all products from the next-lower Lean category.
-/
instance LeanCat.HasAllProducts
    : HasAllProducts.{ℓ} LeanCat.{ℓ}
:= @HasAllLimits.HasAllProducts.{ℓ} LeanCat.{ℓ} @LeanCat.HasAllLimits.{ℓ (ℓ + 1)}

/-! #brief The Lean categories have all finite products.
-/
instance LeanCat.HasAllFiniteProducts
    : @HasAllFiniteProducts LeanCat.{ℓ}
:= { prod
      := λ LeanHasFinal c₁ c₂
         , { obj := { obj := prod c₁ c₂
                    , hom := λ b, begin cases b, apply prod.snd, apply prod.fst end
                    , triangle := λ b₁ b₂ f, begin cases f with b, cases b, apply rfl, apply rfl end
                    }
           , hom
              := λ prd
                 , { mediate
                      := λ cn, { fst := prd^.hom bool.tt cn
                               , snd := prd^.hom bool.ff cn
                               }
                   , factor := λ b, begin cases b, apply rfl, apply rfl end
                   }
           , uniq := λ x h, begin apply ConeHom.eq, apply funext, intro cn, dsimp, exact sorry end
           }
   , prod_id_left₁
      := λ LeanHasFinal T, prod.snd
   , prod_id_left₂
      := λ LeanHasFinal T t
         , { fst := sorry -- punit.star
           , snd := t
           }
   , prod_id_left
      := λ LeanHasFinal T
         , { id₁ := sorry -- begin apply funext, intro x, cases x with x₁ x₂, cases x₁, apply rfl end
           , id₂ := begin apply funext, intro x, apply rfl end
           }
   , prod_id_right₁ := λ LeanHasFinal T, prod.fst
   , prod_id_right₂
      := λ LeanHasFinal T t
         , { fst := t
           , snd := sorry -- punit.star
           }
   , prod_id_right
      := λ LeanHasFinal T
         , { id₁ := sorry -- begin apply funext, intro x, cases x with x₁ x₂, cases x₂, apply rfl end
           , id₂ := begin apply funext, intro x, apply rfl end
           }
   }


/-! #brief The Lean categories are cartesian monoidal.
-/
@[reducible] definition LeanCat.CartesianMonoidal
      [Lean_HasFinal : HasFinal LeanCat.{ℓ}]
    : IsMonoidal LeanCat.{ℓ} (PairFun LeanCat.{ℓ}) (final LeanCat.{ℓ})
:= HasAllFiniteProducts.Monoidal

/-! #brief The Lean categories are cartesian monoidal.
-/
@[reducible] definition LeanCat.CartesianSymmetric
    : IsSymmetric LeanCat.{ℓ}
                  LeanCat.CartesianMonoidal
                  PairFun.BraidTrans
:= HasAllFiniteProducts.Symmetric

/-! #brief Internal hom in a Lean category.
-/
@[reducible] definition LeanCat.InternalHom
    : [[LeanCat.{ℓ}]] → LeanCat.{ℓ} ⇉⇉ LeanCat.{ℓ}
:= λ y, HomFun.{(ℓ + 1) (ℓ + 1)} LeanCat.{ℓ} □□ LeftProdFun y LeanCat.{ℓ}

/-! #brief The Lean categories are cartesian closed.
-/
@[reducible] definition LeanCat.CartesianClosed
    : IsClosedMonoidal LeanCat.{ℓ}
                       LeanCat.CartesianSymmetric.{ℓ}
                       LeanCat.InternalHom.{ℓ}
:= λ X, { counit
           := { component := λ Y fx, fx^.fst fx^.snd
              , transport := λ Y₁ Y₂ f , begin apply funext, intro gx, apply rfl end
              }
        , unit
           := { component := λ Y y x, { fst := y, snd := x }
              , transport := λ Y₁ Y₂ f, begin apply funext, intro gx, apply rfl end
              }
        , id_left := λ Y, begin apply funext, intro yx, cases yx, apply rfl end
        , id_right := λ Y, begin apply funext, intro yx, apply rfl end
        }

end qp
