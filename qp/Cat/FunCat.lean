/- ----------------------------------------------------------------------------
Properties of FunCat.
---------------------------------------------------------------------------- -/

import .basic
import .Cone
import .SubObjClass

namespace qp
universe variables ℓobj ℓhom ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂ ℓobj₃ ℓhom₃



/- ----------------------------------------------------------------------------
The constant functor.
---------------------------------------------------------------------------- -/

/-! #brief The constant functor.
-/
@[reducible] definition Fun.const (B : Cat.{ℓobj₁ ℓhom₁}) {C : Cat.{ℓobj₂ ℓhom₂}}
    (c : [[C]])
    : B ⇉⇉ C
:= { obj := λ b, c
   , hom := λ b₁ b₂ f, ⟨⟨c⟩⟩
   , hom_id := λ b, rfl
   , hom_circ := λ b₁ b₂ b₃ g f, by simp
   }

/-! #brief The constant natural transformation between two constant functors.
-/
@[reducible] definition Fun.const.NatTrans (B : Cat.{ℓobj₁ ℓhom₁}) {C : Cat.{ℓobj₂ ℓhom₂}}
    {c₁ c₂ : [[C]]}
    (f : c₁ →→ c₂)
    : Fun.const B c₁ ↣↣ Fun.const B c₂
:= { component := λ b, f
   , transport := λ b₁ b₂ g, begin dsimp, simp end
   }

/-! #brief The constant natural transformation is monic when the underlying hom is monic.
-/
theorem Fun.const.NatTrans.IsMonic {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {c₁ c₂ : [[C]]}
    {f : c₁ →→ c₂}
    (f_monic : IsMonic f)
    : @IsMonic (FunCat B C) _ _ (Fun.const.NatTrans B f)
:= λ F η₁ η₂ ωη
   , begin
       apply NatTrans.eq, intro b,
       apply f_monic,
       apply congr_fun (congr_arg NatTrans.component ωη)
     end



/- ----------------------------------------------------------------------------
Monics in FunCat.
---------------------------------------------------------------------------- -/

/-! #brief If a natural transformation is monic in FunCat, its components are also monic.
-/
theorem FunCat.NatTrans.IsMonic {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {F₁ F₂ : [[FunCat B C]]}
    {η : F₁ ↣↣ F₂}
    (η_monic : @IsMonic (FunCat B C) F₁ F₂ η)
    : ∀ (b : [[B]])
      , IsMonic (η b)
:= λ b c f₁ f₂ ω
   , sorry


/- ----------------------------------------------------------------------------
Final.
---------------------------------------------------------------------------- -/

/-! #brief Final objects in functor categories.
-/
@[reducible] definition FunCat.Final (B : Cat.{ℓobj₁ ℓhom₁}) {C : Cat.{ℓobj₂ ℓhom₂}}
    {c : [[C]]} (c_final : IsFinal C c)
    : IsFinal (FunCat B C) (Fun.const B c)
:= { final
      := λ F
         , { component := λ b, c_final (F b)
           , transport := λ b₁ b₂ f, begin simp, apply c_final^.uniq end
           }
   , uniq
      := λ F η
         , begin
             apply NatTrans.eq,
             intro b,
             dsimp,
             apply c_final^.uniq
           end
   }



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

/-! #brief The swap of a cone.
-/
@[reducible] definition FunCat.swap.IsCone {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
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
             rw [D^.circ_assoc, -IsLimit.mediate_factor (D_HasAllLimits^.is_limit c₃)],
             rw [-D^.circ_assoc, -IsLimit.mediate_factor (D_HasAllLimits^.is_limit c₂)],
             dsimp, simp [Fun.hom_circ, Cat.circ_assoc]
           end
   }

/-! #brief Building a cone with LimitFun □□ FunCat.swap.
-/
@[reducible] definition LimitFun_swap.IsCone {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    (D_HasAllLimits : HasAllLimits.{ℓobj ℓhom} D)
    {B : Cat.{ℓobj ℓhom}} (F : B ⇉⇉ FunCat C D)
    : IsCone F (LimitFun B D_HasAllLimits □□ FunCat.swap F)
:= { proj
      := λ x, { component := λ c, by apply IsLimit.proj (D_HasAllLimits^.is_limit (FunCat.swap F c)) x
              , transport := λ c₁ c₂ f, by rw -(IsLimit.mediate_factor (D_HasAllLimits^.is_limit (FunCat.swap F c₂)) _)
              }
   , triangle
      := λ x₁ x₂ f
         , begin
             apply NatTrans.eq, intro c, dsimp,
             apply IsLimit.triangle (D_HasAllLimits^.is_limit (FunCat.swap F c)) f
           end
   }

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
         , { is_cone := LimitFun_swap.IsCone D_HasAllLimits F
           , is_final
              := { final
                    := λ cone
                       , { mediate
                            := { component
                                  := λ c
                                     , IsLimit.mediate (D_HasAllLimits^.is_limit (FunCat.swap F c))
                                        (FunCat.swap.IsCone D_HasAllLimits F cone c)
                               , transport := λ c₁ c₂ f, sorry
                               }
                         , factor
                            := λ x
                               , begin
                                   apply NatTrans.eq, intro c, dsimp,
                                   rw -IsLimit.mediate_factor (D_HasAllLimits^.is_limit (FunCat.swap F c)),
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



/- ----------------------------------------------------------------------------
Subobject classifiers.
---------------------------------------------------------------------------- -/

/-! #brief Subobject classifiers.
-/
@[reducible] definition FunCat.SubObjClass {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {cl : [[C]]} {cl_final : IsFinal C cl}
    (C_SubObjClass : SubObjClass C cl_final)
    : SubObjClass (FunCat B C) (FunCat.Final B cl_final)
:= { Ω := Fun.const B C_SubObjClass^.Ω
   , true := Fun.const.NatTrans B C_SubObjClass^.true
   , true_monic := Fun.const.NatTrans.IsMonic C_SubObjClass^.true_monic
   , char
      := λ U X η η_monic
         , { component
              := λ b
                 , C_SubObjClass^.char (η b)
                    (λ c u₁ u₂ ω, begin exact sorry end)
           , transport := λ b₁ b₂ f, begin exact sorry end
           }
   , char_pullback
      := λ U X f f_monic
         , IsPullback.show _ _ _ _
           (λ cone
            , { component := λ b,
                  IsLimit.mediate (C_SubObjClass^.char_pullback (f b) (FunCat.NatTrans.IsMonic f_monic b))^.is_limit
                    { proj := λ x, begin exact sorry end
                    , triangle := begin exact sorry end
                    }
              , transport := begin exact sorry end
              })
           begin exact sorry end
           begin intro cone, exact sorry end
           begin intro cone, exact sorry end
           begin intros cone h, exact sorry end
   , char_uniq := begin exact sorry end
   }

end qp
