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

/-! #brief Helper for FunCat.HasAllLimits.limit.
-/
@[reducible] definition FunCat.HasAllLimits.hom_cone {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    {B : Cat.{ℓobj ℓhom}} (F : B ⇉⇉ FunCat C D)
    (limit : [[C]] → [[D]])
    (is_limit : ∀ (c : [[C]]), IsLimit (FunCat.swap F c) (limit c))
    {c₁ c₂ : [[C]]} (f : c₁ →→ c₂)
    : IsCone (FunCat.swap F c₂) (limit c₁)
:= { proj := λ b, (FunCat.swap F ↗ f) b ∘∘ IsLimit.proj (is_limit c₁) b
   , triangle := λ x₁ x₂ g
                 , begin
                     simp [Cat.circ_assoc],
                     rw IsLimit.triangle _ g,
                     simp [Cat.circ_assoc],
                     rw (FunCat.swap F ↗ f)^.transport
                   end
   }

/-! #brief The limiting object of a diagram of functors.
-/
@[reducible] definition FunCat.HasAllLimits.limit {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    {B : Cat.{ℓobj ℓhom}} (F : B ⇉⇉ FunCat C D)
    (limit : [[C]] → [[D]])
    (is_limit : ∀ (c : [[C]]), IsLimit (FunCat.swap F c) (limit c))
    : [[FunCat C D]]
:= { obj := limit
   , hom
      := λ c₁ c₂ f
         , IsLimit.mediate (is_limit c₂) (FunCat.HasAllLimits.hom_cone F limit is_limit f)
   , hom_id
      := λ c
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
             rw [D^.circ_assoc, -IsLimit.factor (is_limit c₃)],
             rw [-D^.circ_assoc, -IsLimit.factor (is_limit c₂)],
             dsimp, simp [Fun.hom_circ, Cat.circ_assoc]
           end
   }

/-! #brief The limiting object is a bona-fide cone.
-/
@[reducible] definition FunCat.HasAllLimits.limit_is_cone {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    {B : Cat.{ℓobj ℓhom}} (F : B ⇉⇉ FunCat C D)
    (limit : [[C]] → [[D]])
    (is_limit : ∀ (c : [[C]]), IsLimit (FunCat.swap F c) (limit c))
    : IsCone F (FunCat.HasAllLimits.limit F limit is_limit)
:= { proj := λ x, { component := λ c, by apply IsLimit.proj (is_limit c) x
                  , transport := λ c₁ c₂ f, by rw -(IsLimit.factor (is_limit c₂) _)
                  }
   , triangle := λ x₁ x₂ f, begin apply NatTrans.eq, intro c, dsimp, apply IsLimit.triangle (is_limit c) f end
   }

/-! #brief The limiting object is a bona-fide final.
-/
@[reducible] definition FunCat.HasAllLimits.limit_is_final {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    {B : Cat.{ℓobj ℓhom}} (F : B ⇉⇉ FunCat C D)
    (limit : [[C]] → [[D]])
    (is_limit : ∀ (c : [[C]]), IsLimit (FunCat.swap F c) (limit c))
    : IsFinal (ConeCat F) (FunCat.HasAllLimits.limit_is_cone F limit is_limit)
:= { final := λ cone, { mediate := { component := λ c, sorry
                                   , transport := sorry
                                   }
                      , factor := sorry
                      }
   , uniq := sorry
   }

/-! #brief The limiting object is a bona-fide limit.
-/
@[reducible] definition FunCat.HasAllLimits.is_limit {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    {B : Cat.{ℓobj ℓhom}} (F : B ⇉⇉ FunCat C D)
    (limit : [[C]] → [[D]])
    (is_limit : ∀ (c : [[C]]), IsLimit (FunCat.swap F c) (limit c))
    : IsLimit F (FunCat.HasAllLimits.limit F limit is_limit)
:= { is_cone := FunCat.HasAllLimits.limit_is_cone F limit is_limit
   , is_final := FunCat.HasAllLimits.limit_is_final F limit is_limit
   }

/-! #brief The functor category has as many limits as the codomain category.
-/
@[reducible] definition FunCat.HasAllLimits {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    (D_HasAllLimits : HasAllLimits.{ℓobj ℓhom} D)
    : HasAllLimits.{ℓobj ℓhom} (FunCat C D)
:= { limit := λ {B : Cat.{ℓobj ℓhom}} (F : B ⇉⇉ FunCat C D)
              , FunCat.HasAllLimits.limit F
                 (λ c, D_HasAllLimits^.limit (FunCat.swap F c))
                 (λ c, D_HasAllLimits^.is_limit (FunCat.swap F c))
   , is_limit := λ {B : Cat.{ℓobj ℓhom}} (F : B ⇉⇉ FunCat C D)
                 , FunCat.HasAllLimits.is_limit F
                    (λ c, D_HasAllLimits^.limit (FunCat.swap F c))
                    (λ c, D_HasAllLimits^.is_limit (FunCat.swap F c))
   }

end qp
