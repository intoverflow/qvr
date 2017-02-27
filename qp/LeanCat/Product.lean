/- ----------------------------------------------------------------------------
Products in LeanCat.
---------------------------------------------------------------------------- -/

import ..Cat
import .Limit

namespace qp



/- ----------------------------------------------------------------------------
Products.
---------------------------------------------------------------------------- -/

/-! #brief The Lean categories have all products from the next-lower Lean category.
-/
@[reducible] definition {ℓ} LeanCat.HasAllProducts
    : HasAllProducts.{ℓ} LeanCat.{ℓ}
:= @HasAllLimits.HasAllProducts.{ℓ} LeanCat.{ℓ} @LeanCat.HasAllLimits.{ℓ (ℓ + 1)}

namespace OLD_OLD
    /-! #brief The finite product type.
    -/
    definition {ℓ} LeanCat.Prod
        : list [[LeanCat.{ℓ}]] → [[LeanCat.{ℓ}]]
    | list.nil := punit
    | (T :: TS) := prod T (LeanCat.Prod TS)

    /-! #brief Projection from the product type.
    -/
    @[reducible] definition {ℓ} LeanCat.Prod.π
        : ∀ {factors : list [[LeanCat.{ℓ}]]}
            (n : fin (list.length factors))
            (p : LeanCat.Prod factors)
            , list.get factors n
    | list.nil n p := fin.zero_elim n
    | (T :: TT) (fin.mk 0 ω) (prod.mk t p) := t
    | (T :: TT) (fin.mk (nat.succ n) ω) (prod.mk t p)
    := LeanCat.Prod.π { val := n, is_lt := sorry } p

    /-! #brief Construct a LeanCat.Prod by providing the factors.
    -/
    @[reducible] definition {ℓ} LeanCat.Prod.mk
        : ∀ {factors : list [[LeanCat.{ℓ}]]}
            (p : ∀ (n : fin (list.length factors)), list.get factors n)
        , LeanCat.Prod factors
    | list.nil p := punit.star
    | (f :: fs) p := { fst := p { val := 0, is_lt := sorry }
                    , snd := @LeanCat.Prod.mk fs (λ n, cast sorry (p { val := nat.succ n^.val, is_lt := sorry }))
                    }
end OLD_OLD

/-! #brief The Lean categories have all finite products.
-/
@[reducible] definition {ℓ} LeanCat.HasAllFiniteProducts
    : @HasAllFiniteProducts LeanCat.{ℓ} LeanCat.Final
:= { prod
      := λ c₁ c₂, { obj := { obj := prod c₁ c₂
                        , proj := λ b, begin cases b, apply prod.snd, apply prod.fst end
                        , triangle := λ b₁ b₂ f, begin cases f with b, cases b, apply rfl, apply rfl end
                        }
                  , final := λ prd
                             , { mediate
                                  := λ cn, { fst := prd^.proj bool.tt cn
                                           , snd := prd^.proj bool.ff cn
                                           }
                               , factor := λ b, begin cases b, apply rfl, apply rfl end
                               }
                  , uniq := λ x h, begin apply ConeHom.eq, apply funext, intro cn, dsimp, exact sorry end
                  }
   , prod_id_left₁ := λ T, prod.snd
   , prod_id_left₂ := λ T t, { fst := punit.star, snd := t }
   , prod_id_left := λ T, { id₁ := begin apply funext, intro x, cases x with x₁ x₂, cases x₁, apply rfl end
                          , id₂ := begin apply funext, intro x, apply rfl end
                          }
   , prod_id_right₁ := λ T, prod.fst
   , prod_id_right₂ := λ T t, { fst := t, snd := punit.star }
   , prod_id_right := λ T, { id₁ := begin apply funext, intro x, cases x with x₁ x₂, cases x₂, apply rfl end
                           , id₂ := begin apply funext, intro x, apply rfl end
                           }
   }


/-! #brief The Lean categories are cartesian monoidal.
-/
@[reducible] definition {ℓ} LeanCat.CartesianMonoidal
    : IsMonoidal LeanCat.{ℓ}
                 (PairFun LeanCat.HasAllFiniteProducts)
                 punit.{ℓ + 1}
:= HasAllFiniteProducts.Monoidal LeanCat.HasAllFiniteProducts

/-! #brief The Lean categories are cartesian monoidal.
-/
@[reducible] definition {ℓ} LeanCat.CartesianSymmetric
    : IsSymmetric LeanCat.{ℓ}
                  LeanCat.CartesianMonoidal
                  (PairFun.BraidTrans LeanCat.HasAllFiniteProducts)
:= HasAllFiniteProducts.Symmetric LeanCat.HasAllFiniteProducts

/-! #brief Internal hom in a Lean category.
-/
@[reducible] definition {ℓ} LeanCat.InternalHom
    : [[LeanCat.{ℓ}]] → LeanCat.{ℓ} ⇉⇉ LeanCat.{ℓ}
:= λ y, HomFun.{(ℓ + 1) (ℓ + 1)} LeanCat.{ℓ} □□ LeftProdFun y LeanCat.{ℓ}

/-! #brief The Lean categories are cartesian closed.
-/
@[reducible] definition {ℓ} LeanCat.CartesianClosed
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
