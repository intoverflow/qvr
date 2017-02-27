/- ----------------------------------------------------------------------------
The lifting functor.
---------------------------------------------------------------------------- -/

import ..Cat

namespace qp



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

end qp
