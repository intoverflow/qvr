/- ----------------------------------------------------------------------------
Properties of LeanCat.
---------------------------------------------------------------------------- -/

import .basic
import .Cone
import .Monoidal
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
    : LeanCat.{ℓ₁ + 1} ⇉⇉ LeanCat.{(max ℓ₁ ℓ₂) + 1}
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
    : HasAllLimits.{ℓobj ℓhom} LeanCat.{(max (ℓobj + 1) ℓhom)}
:= { limit
      := λ {B : Cat.{ℓobj ℓhom}} (F : B ⇉⇉ LeanCat.{(max (ℓobj + 1) ℓhom)})
         , { g : ∀ (b : [[B]]), F b // ∀ {b₁ b₂ : [[B]]} (f : b₁ →→ b₂), g b₂ = (F ↗ f) (g b₁) }
   , is_limit
      := λ {B : Cat.{ℓobj ℓhom}} (F : B ⇉⇉ LeanCat.{(max (ℓobj + 1) ℓhom)})
         , { is_cone := { proj := λ b g, g^.elt_of b
                        , triangle
                           := λ b₁ b₂ f
                              , begin
                                  dsimp, apply pfunext, intro g,
                                  apply g^.has_property
                                end
                        }
           , is_final := { final := λ cone, { mediate := λ c, ⟨ λ b, (cone b) c
                                                              , λ b₁ b₂ f, begin dsimp, rw cone^.is_cone^.triangle end
                                                              ⟩
                                            , factor := λ x, rfl
                                            }
                         , uniq
                            := λ cone h
                               , begin
                                   apply ConeHom.eq,
                                   apply pfunext, intro c,
                                   exact sorry
                                  --  apply subtype.eq,
                                  --  dsimp,
                                  --  apply funext, intro x,
                                  --  rw h^.factor
                                 end
                         }
           }
   }



/- ----------------------------------------------------------------------------
Initial and final objects.
---------------------------------------------------------------------------- -/

/-! #brief poly_empty is an initial object in LeanCat.
-/
@[reducible] definition {ℓ} LeanCat.init : IsInit LeanCat.{ℓ} pempty.{ℓ}
:= { init := λ A, pempty.elim
   , uniq := λ A f, begin
                      apply pfunext, intro e,
                      exact pempty.elim e
                    end
   }

/-! #brief poly_unit is a final object in LeanCat.
-/
@[reducible] definition {ℓ} LeanCat.final : IsFinal LeanCat.{ℓ} punit.{ℓ}
:= { final := λ A a, punit.star
   , uniq := λ A f, begin
                      apply pfunext, intro a,
                      apply punit.uniq
                    end
   }



/- ----------------------------------------------------------------------------
Products.
---------------------------------------------------------------------------- -/

/-! #brief The Lean categories have all products from the next-lower Lean category.
-/
@[reducible] definition {ℓ} LeanCat.HasAllProducts
    : HasAllProducts.{ℓ} LeanCat.{ℓ + 1}
:= HasAllLimits.HasAllProducts.{ℓ} LeanCat.HasAllLimits.{ℓ (ℓ + 1)}

/-! #brief The finite product type.
-/
definition {ℓ} LeanCat.Prod
    : list [[LeanCat.{ℓ + 1}]] → [[LeanCat.{ℓ + 1}]]
| [] := punit
| (T :: TS) := prod T (LeanCat.Prod TS)

/-! #brief Projection from the product type.
-/
@[reducible] definition {ℓ} LeanCat.Prod.π
    : ∀ {factors : list [[LeanCat.{ℓ + 1}]]}
        (n : fin (list.length factors))
        (p : LeanCat.Prod factors)
        , list.get factors n
| [] n p := fin.zero_elim n
| (T :: TT) (fin.mk 0 ω) (prod.mk t p) := t
| (T :: TT) (fin.mk (nat.succ n) ω) (prod.mk t p)
:= LeanCat.Prod.π { val := n, is_lt := sorry } p

/-! #brief Construct a LeanCat.Prod by providing the factors.
-/
@[reducible] definition {ℓ} LeanCat.Prod.mk
    : ∀ {factors : list [[LeanCat.{ℓ + 1}]]}
        (p : ∀ (n : fin (list.length factors)), list.get factors n)
      , LeanCat.Prod factors
| [] p := punit.star
| (f :: fs) p := { fst := p { val := 0, is_lt := sorry }
                 , snd := @LeanCat.Prod.mk fs (λ n, cast sorry (p { val := nat.succ n^.val, is_lt := sorry }))
                 }

/-! #brief The Lean categories have all finite products.
-/
@[reducible] definition {ℓ} LeanCat.HasAllFiniteProducts
    : HasAllFiniteProducts LeanCat.{ℓ + 1}
:= { prod := LeanCat.Prod
   , is_prod
      := λ factors
         , { is_cone
              := { proj := LeanCat.Prod.π
                 , triangle := sorry
                 }
           , is_final
              := { final
                    := λ cone
                       , { mediate := λ cn, LeanCat.Prod.mk (λ n, cone^.is_cone^.proj n cn)
                         , factor := sorry
                         }
                 , uniq := sorry
                 }
           }
   }

/-! #brief The Lean categories are cartesian monoidal.
-/
@[reducible] definition {ℓ} LeanCat.CartesianMonoidal
    : IsMonoidal LeanCat.{ℓ + 1}
                 (HasAllFiniteProducts.PairFun LeanCat.HasAllFiniteProducts)
                 punit.{ℓ + 1}
:= HasAllFiniteProducts.Monoidal LeanCat.HasAllFiniteProducts

/-! #brief The Lean categories are cartesian monoidal.
-/
@[reducible] definition {ℓ} LeanCat.CartesianSymmetric
    : IsSymmetric LeanCat.{ℓ + 1}
                  LeanCat.CartesianMonoidal
                  (HasAllFiniteProducts.PairFun.BraidTrans LeanCat.HasAllFiniteProducts)
:= HasAllFiniteProducts.Symmetric LeanCat.HasAllFiniteProducts

/-! #brief Internal hom in a Lean category.
-/
@[reducible] definition {ℓ} LeanCat.InternalHom
    : [[LeanCat.{ℓ}]] → LeanCat.{ℓ} ⇉⇉ LeanCat.{ℓ}
:= λ y, HomFun.{ℓ ℓ} LeanCat.{ℓ} □□ LeftProdFun y LeanCat.{ℓ}

--set_option pp.universes true
/-! #brief The Lean categories are cartesian closed.
-/
@[reducible] definition {ℓ} LeanCat.CartesianClosed
    : IsClosedMonoidal LeanCat.{ℓ + 1}
                       LeanCat.CartesianSymmetric.{ℓ}
                       LeanCat.InternalHom.{ℓ + 1}
:= λ X, { counit
           := { component := λ Y fx, fx^.fst fx^.snd^.fst
              , transport
                 := λ Y₁ Y₂ f
                    , begin
                        apply funext, intro gx,
                        dsimp,
                        apply sorry
                      end
              }
        , unit
           := { component := λ Y y x, ⟨y, x, punit.star⟩
              , transport
                 := λ Y₁ Y₂ f
                    , begin apply funext, intro gx,
                        apply sorry
                      end
              }
        , id_left := λ Y, begin apply sorry end
        , id_right := λ Y, begin apply sorry end
        }

end qp
