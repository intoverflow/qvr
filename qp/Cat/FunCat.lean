/- ----------------------------------------------------------------------------
Properties of FunCat.
---------------------------------------------------------------------------- -/

import .basic
import .Cone

namespace qp
universe variables ℓobj ℓhom ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂ ℓobj₃ ℓhom₃



/- ----------------------------------------------------------------------------
Swapping the argument-order of functors into a functor category.
---------------------------------------------------------------------------- -/

/-! #brief The swap of a functor into a functor category.
-/
@[reducible] definition FunCat.swap {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    (F : B ⇉⇉ FunCat C D)
    : C ⇉⇉ FunCat B D
:= { obj := λ c, { obj := λ b, F b c
                 , hom := λ b₁ b₂ f, (F ↗ f) c
                 , hom_id := λ b, begin dsimp, simp end
                 , hom_circ := λ b₁ b₂ b₃ g f, begin dsimp, simp [Fun.hom_circ] end
                 }
   , hom := λ c₁ c₂ f, { component := λ b, F b ↗ f
                       , transport := λ b₁ b₂ g, begin dsimp, simp [NatTrans.transport] end
                       }
   , hom_id := λ c, begin apply NatTrans.eq, intro b, dsimp, simp end
   , hom_circ := λ c₁ c₂ c₃ g f, begin apply NatTrans.eq, intro b, dsimp, simp [Fun.hom_circ] end
   }



/- ----------------------------------------------------------------------------
Limits.
---------------------------------------------------------------------------- -/

/-! #brief The cone through which the limiting functor mediates.
-/
@[reducible] definition LimitFun.mediating_cone (C : Cat.{ℓobj ℓhom}) {D : Cat.{ℓobj₁ ℓhom₁}}
    (D_HasAllLimits : HasAllLimits.{ℓobj ℓhom} D)
    (F G : [[FunCat C D]])
    (η : F ↣↣ G)
    : IsCone G (D_HasAllLimits^.limit F)
:= { proj := λ c, η c ∘∘ IsLimit.proj (D_HasAllLimits^.is_limit F) c
   , triangle
      := λ c₁ c₂ f
         , begin
             rw IsLimit.triangle (D_HasAllLimits^.is_limit F) f,
             simp [Cat.circ_assoc, NatTrans.transport]
           end
   }

/-! #brief The limit functor.
-/
@[reducible] definition LimitFun (B : Cat.{ℓobj ℓhom}) {D : Cat.{ℓobj₁ ℓhom₁}}
    (D_HasAllLimits : HasAllLimits.{ℓobj ℓhom} D)
    : FunCat B D ⇉⇉ D
:= { obj := λ F, D_HasAllLimits^.limit F
   , hom
      := λ F G η
         , IsLimit.mediate (D_HasAllLimits^.is_limit G)
            (LimitFun.mediating_cone B D_HasAllLimits F G η)
   , hom_id
      := λ F
         , begin
             apply eq.symm,
             apply IsLimit.mediate_uniq, intro x,
             dsimp, simp
           end
   , hom_circ
      := λ c₁ c₂ c₃ g f
         , begin
             apply eq.symm,
             apply IsLimit.mediate_uniq, intro x,
             rw [D^.circ_assoc, -IsLimit.factor (D_HasAllLimits^.is_limit c₃)],
             rw [-D^.circ_assoc, -IsLimit.factor (D_HasAllLimits^.is_limit c₂)],
             dsimp, simp [Fun.hom_circ, Cat.circ_assoc]
           end
   }

/-! #brief The swap of a cone.
-/
@[reducible] definition LimitFun.swapCone {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    (D_HasAllLimits : HasAllLimits.{ℓobj ℓhom} D)
    {B : Cat.{ℓobj ℓhom}}
    (F : B⇉⇉FunCat C D)
    (cone : [[ConeCat F]])
    (c : [[C]])
    : IsCone (FunCat.swap F c) (BxCone.cone cone c)
:= { proj := λ x, (cone^.is_cone^.proj x) c
   , triangle
      := λ x₁ x₂ f
         , begin
             dsimp,
             rw (IsCone.triangle (BxCone.is_cone cone) f)
             end
   }          


notation `&&&` x `::` y `&&&` := Fun.mk x y _ _
notation `!!!` x `!!!` := IsCone.mk x _
notation `???` x `???` := NatTrans.mk x _
/-! #brief The functor category has as many limits as the codomain category.
-/
@[reducible] definition FunCat.HasAllLimits {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    (D_HasAllLimits : HasAllLimits.{ℓobj ℓhom} D)
    : HasAllLimits.{ℓobj ℓhom} (FunCat C D)
:= { limit
      := λ {B : Cat.{ℓobj ℓhom}} (F : B ⇉⇉ FunCat C D)
         , LimitFun B D_HasAllLimits □□ FunCat.swap F
   , is_limit
      := λ {B : Cat.{ℓobj ℓhom}} (F : B ⇉⇉ FunCat C D)
         , { is_cone
              := { proj
                    := λ x
                       , { component := λ c, by apply IsLimit.proj (D_HasAllLimits^.is_limit (FunCat.swap F c)) x
                         , transport := λ c₁ c₂ f, by rw -(IsLimit.factor (D_HasAllLimits^.is_limit (FunCat.swap F c₂)) _)
                         }
                 , triangle
                    := λ x₁ x₂ f
                       , begin
                           apply NatTrans.eq, intro c, dsimp,
                           apply IsLimit.triangle (D_HasAllLimits^.is_limit (FunCat.swap F c)) f
                         end
                 }
           , is_final
              := { final
                    := λ cone
                       , { mediate
                            := { component
                                  := λ c
                                     , IsLimit.mediate (D_HasAllLimits^.is_limit (FunCat.swap F c))
                                        (LimitFun.swapCone D_HasAllLimits F cone c)
                               , transport := λ c₁ c₂ f, sorry
                               }
                         , factor
                            := λ x
                               , begin
                                   apply NatTrans.eq, intro c, dsimp,
                                   rw -IsLimit.factor (D_HasAllLimits^.is_limit (FunCat.swap F c)),
                                 end
                         }
                 , uniq
                    := λ cone h
                       , begin
                           apply ConeHom.eq, apply NatTrans.eq, intro c,
                           apply IsLimit.mediate_uniq, intro x,
                           exact (congr_arg (λ η, NatTrans.component η c) (h^.factor))
                         end
                 }
           }
   }

end qp
