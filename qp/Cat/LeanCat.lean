/- --- OLD



/- ----------------------------------------------------------------------------
Properties of LeanCat.
---------------------------------------------------------------------------- -/

import .basic
import .Cone
import .Monoidal
import .Pullback
import .DepProduct
import .Product
import .Fun

namespace qp
universe variables ℓobj ℓhom



/- ----------------------------------------------------------------------------
Lifting.
---------------------------------------------------------------------------- -/

/-! #brief Action of the lifting functor on types.
-/
inductive {ℓ₁ ℓ₂} Lift (T : Type ℓ₁) : Type (max ℓ₁ ℓ₂)
| lift : T → Lift

/-! #brief Action of the lifting functor on functions.
-/
@[reducible] definition {ℓ₁₁ ℓ₁₂ ℓ₂₁ ℓ₂₂} Lift.fun {T₁ : Type ℓ₁₁} {T₂ : Type ℓ₂₁}
    (f : T₁ → T₂)
    : Lift.{ℓ₁₁ ℓ₁₂} T₁ → Lift.{ℓ₂₁ ℓ₂₂} T₂
| (Lift.lift t₁) := Lift.lift (f t₁)

/-! #brief The binding action of the lifting functor.
-/
@[reducible] definition {ℓ₁₁ ℓ₁₂ ℓ₂₁ ℓ₂₂} Lift.bind {T₁ : Type ℓ₁₁} {T₂ : Type ℓ₂₁}
    : Lift.{ℓ₁₁ ℓ₁₂} T₁ → (T₁ → Lift.{ℓ₂₁ ℓ₂₂} T₂) → Lift.{ℓ₂₁ ℓ₂₂} T₂
| (Lift.lift t₁) f := f t₁

/-! #brief The lifting functor.
-/
@[reducible] definition {ℓ₁ ℓ₂} LiftFun
    : LeanCat.{ℓ₁} ⇉⇉ LeanCat.{max ℓ₁ ℓ₂}
:= { obj := Lift.{ℓ₁ ℓ₂}
   , hom := @Lift.fun
   , hom_id
      := λ T
         , begin
             apply funext,
             intro lift_t,
             cases lift_t,
             apply rfl
           end
   , hom_circ
      := λ X Y Z g f
         , begin
             apply funext,
             intro lift_t,
             cases lift_t,
             apply rfl
           end
   }

/-! #brief The lifting functor preserves all limits.

NOTE: maybe it doesn't?
-/
/-
@[reducible] definition {ℓ₁ ℓ₂} LiftFun.PreservesAllLimits
    : PreservesLimits.{ℓobj ℓhom} LiftFun.{ℓ₁ ℓ₂}
:= { limit
      := λ B F T lim
         , { is_cone
              := { proj := λ b t, Lift.fun (IsLimit.proj lim b) t
                 , triangle
                    := λ b₁ b₂ f
                       , begin
                           apply funext, intro lift_t,
                           rw (IsLimit.triangle lim f),
                           cases lift_t,
                           apply rfl
                         end
                 }
           , is_final
              := { final
                    := λ cone
                       , { mediate := λ cn, Lift.lift (@IsLimit.mediate _ _ _ _ lim begin cases cone, end
                                                        begin
                                                          exact sorry
                                                        end
                                                        begin
                                                        end)
                         , factor := sorry
                         }
                 , uniq := sorry
                 }
           }
   }
-/



/- ----------------------------------------------------------------------------
Limits.
---------------------------------------------------------------------------- -/

/-! #brief For certain type levels, LeanCat has all limits.
-/
definition LeanCat.HasAllLimits
    : HasAllLimits.{ℓobj ℓhom} LeanCat.{ℓobj}
:= λ {B : Cat.{ℓobj ℓhom}} (F : B ⇉⇉ LeanCat.{ℓobj})
   , Limit.show F
      { g : ∀ (b : [[B]]), F b // ∀ {b₁ b₂ : [[B]]} (f : b₁ →→ b₂), g b₂ = (F ↗ f) (g b₁) }
      (λ b g, g^.elt_of b)
      (λ cone c, { elt_of := λ b, cone^.proj b c
                 , has_property := λ b₁ b₂ f, begin dsimp, rw cone^.triangle end
                 })
      (λ x₁ x₂ f, begin dsimp, apply pfunext, intro g, apply g^.has_property end)
      (λ cone x, rfl)
      (λ cone h, begin apply funext, intro c, exact sorry end)



/- ----------------------------------------------------------------------------
Initial and final objects.
---------------------------------------------------------------------------- -/

/-! #brief pempty is an initial object in LeanCat.
-/
@[reducible] definition {ℓ} LeanCat.Init
    : Init LeanCat.{ℓ}
:= { obj := pempty.{ℓ + 1}
   , init := λ A, pempty.elim
   , uniq := λ A f, begin
                      apply pfunext, intro e,
                      exact pempty.elim e
                    end
   }

/-! #brief punit is a final object in LeanCat.
-/
@[reducible] definition {ℓ} LeanCat.Final
    : Final LeanCat.{ℓ}
:= { obj := punit.{ℓ + 1}
   , final := λ A a, punit.star
   , uniq := λ A f, begin
                      apply pfunext, intro a,
                      apply punit.uniq
                    end
   }



/- ----------------------------------------------------------------------------
Pullbacks.
---------------------------------------------------------------------------- -/

/-! #brief The Lean categories have all pullbacks.
-/
@[reducible] definition {ℓ} LeanCat.HasAllPullbacks
    : HasAllPullbacks LeanCat.{ℓ}
:= λ A B Z ga gb
   , @Pullback.show LeanCat.{ℓ} A B Z ga gb
      { ab : A × B // ga ab^.fst = gb ab^.snd }
      (λ ab, ab^.elt_of^.fst)
      (λ ab, ab^.elt_of^.snd)
      (λ cone cn, { elt_of := { fst := cone^.proj CoSpanCat.Obj.a cn
                              , snd := cone^.proj CoSpanCat.Obj.b cn
                              }
                  , has_property := begin dsimp, exact sorry end
                  })
      begin apply funext, intro x, apply x^.has_property end
      (λ cone, rfl)
      (λ cone, rfl)
      (λ cone h, begin apply funext, intro cn, dsimp, exact sorry end)



/- ----------------------------------------------------------------------------
Dependent products.
---------------------------------------------------------------------------- -/

/-! #brief The Lean categories have dependent products.
-/
@[reducible] definition {ℓ} LeanCat.HasAllDepProducts
    : HasAllDepProducts @LeanCat.HasAllPullbacks.{ℓ}
:= λ x y base
   , { dprod := begin end
     , adj := begin end
     }



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



/- ----------------------------------------------------------------------------
Products in the slice categories.
---------------------------------------------------------------------------- -/

/-! #brief Slices of Lean categories have all finite products.
-/
@[reducible] definition {ℓ} LeanCat.Slice.HasAllFiniteProducts
    (T : [[LeanCat.{ℓ}]])
    : HasAllFiniteProducts (SliceCat LeanCat.{ℓ} T) SliceCat.Final
:= { prod := λ c₁ c₂
             , Product.show (bool.pick c₁ c₂)
                { dom := LeanCat.HasAllPullbacks c₁^.hom c₂^.hom
                , hom := c₁^.hom ∘∘ Pullback.π₁ (LeanCat.HasAllPullbacks c₁^.hom c₂^.hom)
                }
                (λ b, bool.cases_on b
                       { hom := Pullback.π₂ (LeanCat.HasAllPullbacks c₁^.hom c₂^.hom)
                       , triangle := begin apply funext, intro ab, dsimp, exact sorry end
                       }
                       { hom := Pullback.π₁ (LeanCat.HasAllPullbacks c₁^.hom c₂^.hom)
                       , triangle := begin apply funext, intro ab, dsimp, exact sorry end
                       })
                (λ cone, { hom := λ cn, { elt_of := { fst := (cone^.proj bool.tt)^.hom cn
                                                    , snd := (cone^.proj bool.ff)^.hom cn
                                                    }
                                        , has_property := sorry
                                        }
                         , triangle := sorry
                         })
                sorry
                sorry
   , prod_id_left₁ := λ U, { hom := λ ab, ab^.elt_of^.snd
                           , triangle := begin apply funext, intro ab, exact sorry end
                           }
   , prod_id_left₂ := λ U, { hom := λ u, { elt_of := { fst := U^.hom u, snd := u }
                                         , has_property := rfl
                                         }
                           , triangle := begin apply funext, intro u, apply rfl end
                           }
   , prod_id_left := λ U, { id₁ := begin apply SliceCat.Hom.eq, apply funext, intro ab, exact sorry end
                          , id₂ := begin apply SliceCat.Hom.eq, apply funext, intro u, apply rfl end
                          }
   , prod_id_right₁ := λ U, { hom := λ ab, ab^.elt_of^.fst
                            , triangle := begin apply funext, intro ab, exact sorry end
                            }
   , prod_id_right₂ := λ U, { hom := λ u, { elt_of := { fst := u, snd := U^.hom u }
                                          , has_property := rfl
                                          }
                            , triangle := begin apply funext, intro u, apply rfl end
                            }
   , prod_id_right := λ U, { id₁ := begin apply SliceCat.Hom.eq, apply funext, intro ab, exact sorry end
                           , id₂ := begin apply SliceCat.Hom.eq, apply funext, intro u, apply rfl end
                           }
   }

/-! #brief Slices of Lean categories are cartesian monoidal.
-/
@[reducible] definition {ℓ} LeanCat.Slice.CartesianMonoidal
    (T : [[LeanCat.{ℓ}]])
    : IsMonoidal (SliceCat LeanCat.{ℓ} T)
                 (PairFun (LeanCat.Slice.HasAllFiniteProducts T))
                 SliceCat.Final^.obj
:= HasAllFiniteProducts.Monoidal (LeanCat.Slice.HasAllFiniteProducts T)

/-! #brief Slices of Lean categories are cartesian monoidal.
-/
@[reducible] definition {ℓ} LeanCat.Slice.CartesianSymmetric
    (T : [[LeanCat.{ℓ}]])
    : IsSymmetric (SliceCat LeanCat.{ℓ} T)
                  (LeanCat.Slice.CartesianMonoidal T)
                  (PairFun.BraidTrans (LeanCat.Slice.HasAllFiniteProducts T))
:= HasAllFiniteProducts.Symmetric (LeanCat.Slice.HasAllFiniteProducts T)

/-! #brief Internal hom in a slice of a Lean category.
-/
@[reducible] definition {ℓ} LeanCat.Slice.InternalHom
    (T : [[LeanCat.{ℓ}]])
    : [[SliceCat LeanCat.{ℓ} T]] → SliceCat LeanCat.{ℓ} T ⇉⇉ SliceCat LeanCat.{ℓ} T
:= λ y, sorry

end qp

---- OLD -/
