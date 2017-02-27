/- ----------------------------------------------------------------------------
Cones and cocones.
---------------------------------------------------------------------------- -/

import .basic
import .FinCat

namespace qp
universe variables ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂ ℓobj₃ ℓhom₃



/- ----------------------------------------------------------------------------
Cones.
---------------------------------------------------------------------------- -/

-- A cone of a functor.
structure Cone
    {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    (F : B ⇉⇉ C)
    : Type (max ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂)
:= (obj : [[C]])
   (proj : ∀ (x : [[B]]), obj →→ F x)
   (triangle : ∀ {x₁ x₂ : [[B]]} (f : x₁ →→ x₂)
               , proj x₂ = (F ↗ f) ∘∘ proj x₁)

/-! #brief Every cone can be used as an object.
-/
@[reducible] instance Cone.has_coe_to_obj
    {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    (F : B ⇉⇉ C)
    : has_coe (Cone F) [[C]]
:= { coe := Cone.obj
   }

-- A homomorphism between cones.
structure ConeHom {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : B ⇉⇉ C}
    (c₁ c₂ : Cone F)
    : Sort (max 1 ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂)
:= (mediate : C^.hom c₁ c₂)
   (factor : ∀ {x : [[B]]}
             , c₁^.proj x = c₂^.proj x ∘∘ mediate)

/-! #brief Helper lemma for proving quality of ConeHoms.
-/
theorem ConeHom.eq {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : B ⇉⇉ C}
    (c₁ c₂ : Cone F)
    : ∀ (h₁ h₂ : ConeHom c₁ c₂)
        (ωmediate : h₁^.mediate = h₂^.mediate)
      , h₁ = h₂
| (ConeHom.mk m f₁) (ConeHom.mk .m f₂) (eq.refl .m)
:= rfl



/- ----------------------------------------------------------------------------
ConeHoms are morphisms of cones.
---------------------------------------------------------------------------- -/

/-! #brief The identity ConeHom.
-/
@[reducible] definition ConeHom.id {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : B ⇉⇉ C} (c : Cone F)
    : ConeHom c c
:= { mediate := ⟨⟨c^.obj⟩⟩
   , factor := λ x, by simp
   }

/-! #brief Composition of ConeHoms.
-/
@[reducible] definition ConeHom.comp {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : B ⇉⇉ C} {c₁ c₂ c₃ : Cone F}
    (g : ConeHom c₂ c₃) (f : ConeHom c₁ c₂)
    : ConeHom c₁ c₃
:= { mediate := g^.mediate ∘∘ f^.mediate
   , factor
      := λ x
         , begin
             --refine eq.trans _ (eq.symm C^.circ_assoc), rw -g^.factor, apply f^.factor end
             calc c₁^.proj x
                      = c₂^.proj x ∘∘ f^.mediate                 : f^.factor
                  ... = (c₃^.proj x ∘∘ g^.mediate) ∘∘ f^.mediate : begin rw [g^.factor], apply rfl end
                  ... = c₃^.proj x∘∘(g^.mediate∘∘f^.mediate)     : by rw C^.circ_assoc
           end
   }

/-! #brief Composition of ConeHoms is associative.
-/
@[simp] theorem ConeHom.comp_assoc {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : B ⇉⇉ C}
    {c₁ c₂ c₃ c₄ : Cone F}
    {h : ConeHom c₃ c₄} {g : ConeHom c₂ c₃} {f : ConeHom c₁ c₂}
    : ConeHom.comp h (ConeHom.comp g f) = ConeHom.comp (ConeHom.comp h g) f
:= begin apply ConeHom.eq, simp [Cat.circ_assoc] end

/-! #brief ConeHom.id is a left-identity for ConeHom.comp.
-/
@[simp] theorem ConeHom.comp_id_left {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : B ⇉⇉ C} {c₁ c₂ : Cone F}
    {f : ConeHom c₁ c₂}
    : ConeHom.comp (ConeHom.id c₂) f = f
:= begin apply ConeHom.eq, simp, apply Cat.circ_id_left end

/-! #brief ConeHom.id is a right-identity for ConeHom.comp.
-/
@[simp] theorem ConeHom.comp_id_right {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : B ⇉⇉ C} {c₁ c₂ : Cone F}
    {f : ConeHom c₁ c₂}
    : ConeHom.comp f (ConeHom.id c₁) = f
:= begin apply ConeHom.eq, simp, apply Cat.circ_id_right end



/- ----------------------------------------------------------------------------
The category of cones.
---------------------------------------------------------------------------- -/

/-! #brief The category of cones.
-/
@[reducible] definition ConeCat {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    (F : B ⇉⇉ C)
    : Cat
:= { obj := Cone F
   , hom := λ c₁ c₂, ConeHom c₁ c₂
   , id := λ c, ConeHom.id c
   , circ := λ c₁ c₂ c₃, ConeHom.comp
   , circ_assoc := λ c₁ c₂ c₃ c₄ h g f, ConeHom.comp_assoc
   , circ_id_left := λ c₁ c₂ f, ConeHom.comp_id_left
   , circ_id_right := λ c₁ c₂ f, ConeHom.comp_id_right
   }



/- ----------------------------------------------------------------------------
Limits.
---------------------------------------------------------------------------- -/

/-! #brief A limit of a functor.
-/
@[reducible] definition Limit {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    (F : B ⇉⇉ C)
    : Type (max 1 ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂)
:= Final (ConeCat F)

/-! #brief Helper for building a limit.
-/
@[reducible] definition Limit.show {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    (F : B ⇉⇉ C)
    (c : [[C]])
    (proj : ∀ (x : [[B]]), c →→ F x)
    (mediate : ∀ (cone : Cone F), C^.hom cone c)
    (ωtriangle : ∀ {x₁ x₂ : [[B]]} (f : x₁ →→ x₂), proj x₂ = (F ↗ f) ∘∘ proj x₁)
    (ωfactor : ∀ (cone : Cone F) {x : [[B]]}, cone^.proj x = proj x ∘∘ mediate cone)
    (ωuniq : ∀ (cone : Cone F) (h : ConeHom cone (Cone.mk c proj @ωtriangle)), h^.mediate = mediate cone)
    : Limit F
:= { obj := { obj := c
            , proj := proj
            , triangle := @ωtriangle
            }
   , final := λ cone, { mediate := mediate cone
                      , factor := @ωfactor cone
                      }
   , uniq := λ cone h, begin apply ConeHom.eq, apply ωuniq end
   }

/-! #brief Every limit can be used as a cone.
-/
@[reducible] definition Limit.has_coe_to_cone {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    (F : B ⇉⇉ C)
    : has_coe (Limit F) (Cone F)
:= { coe := Final.obj
   }

/-! #brief Every limit can be used as an object.
-/
@[reducible] instance Limit.has_coe_to_obj {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    (F : B ⇉⇉ C)
    : has_coe (Limit F) [[C]]
:= { coe := λ x, x^.obj^.obj
   }

/-! #brief The map from the limit to the image of the diagram.
-/
@[reducible] definition Limit.proj {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : B ⇉⇉ C}
    (l : Limit F)
    (x : [[B]])
    : C^.hom l (F x)
:= l^.obj^.proj x

/-! #brief Limit.proj satisfies the triangle equation.
-/
theorem Limit.triangle {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : B ⇉⇉ C} (c : Limit F)
    {x₁ x₂ : [[B]]} (f : x₁ →→ x₂)
    : Limit.proj c x₂ = (F ↗ f) ∘∘ Limit.proj c x₁
:= Cone.triangle c f

/-! #brief The mediating map (in C) from a cone to the limit.
-/
@[reducible] definition Limit.mediate {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : B ⇉⇉ C}
    (c : Limit F) (c' : Cone F)
    : C^.hom c' c
:= (c^.final c')^.mediate

/-! #brief The mediating map has the usual factoring property.
-/
theorem Limit.mediate_factor {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : B ⇉⇉ C}
    (c : Limit F) (c' : Cone F)
    {x : [[B]]}
    : c'^.proj x = Limit.proj c x ∘∘ Limit.mediate c c'
  := by apply ConeHom.factor

/-! #brief The mediating map is unique among maps which factor.
-/
theorem Limit.mediate_uniq {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : B ⇉⇉ C}
    (c : Limit F) (c' : Cone F)
    {f : C^.hom c' c}
    (ωf : ∀ {x : [[B]]}, c'^.proj x = Limit.proj c x ∘∘ f)
    : f = Limit.mediate c c'
:= begin
     dsimp,
     assert lem₁ : f = ConeHom.mediate { mediate := f, factor := @ωf },
     { apply rfl },
     rw lem₁,
     apply congr_arg,
     apply c^.uniq
   end

/-! #brief Limits are unique up to isomorphism.
-/
@[reducible] definition Limit.Iso {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : B ⇉⇉ C}
    (c₁ c₂ : Limit F)
    : Iso (Limit.mediate c₂ c₁)
          (Limit.mediate c₁ c₂)
:= let iso := Final.Iso c₁ c₂
   in { id₁ := congr_arg ConeHom.mediate iso^.id₁
      , id₂ := congr_arg ConeHom.mediate iso^.id₂
      }



/- ----------------------------------------------------------------------------
More definitions about limits.
---------------------------------------------------------------------------- -/

-- Notion of when a functor preserves limits.
structure PreservesLimits {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    (F : C ⇉⇉ D)
    : Type ((max ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂ ℓobj₃ ℓhom₃) + 1)
:= (limit : ∀ {B : Cat.{ℓobj₁ ℓhom₁}} (D : Fun B C)
              (c : Limit D)
            , Limit (F □□ D))
   (limit_eq : ∀ {B : Cat.{ℓobj₁ ℓhom₁}} (D : Fun B C)
                 (c : Limit D)
               , (limit D c)^.obj^.obj = F c)

/-! #brief A witness that a category has all limits.
-/
@[reducible] definition HasAllLimits
    (C : Cat.{ℓobj₂ ℓhom₂})
    : Type (max ((max ℓobj₁ ℓhom₁) + 1) ℓobj₂ ℓhom₂)
:= ∀ {B : Cat.{ℓobj₁ ℓhom₁}}
     (F : B ⇉⇉ C)
   , Limit F

/-! #brief A witness that a category has all finite limits.
-/
@[reducible] definition HasAllFiniteLimits
    (C : Cat.{ℓobj₂ ℓhom₂})
    : Type (max ((max ℓobj₁ ℓhom₁) + 1) ℓobj₂ ℓhom₂)
:= ∀ {B : Cat.{ℓobj₁ ℓhom₁}} (B_Fin : Cat.Fin B)
     (F : B ⇉⇉ C)
   , Limit F

/-! #brief Categories with all limits have all (finite) limits.
-/
definition HasAllLimits.HasAllFiniteLimits
    (C : Cat.{ℓobj₂ ℓhom₂})
    (C_HasAllLimits : HasAllLimits C)
    : HasAllFiniteLimits C
:= λ B B_Fin F, C_HasAllLimits F



/- ----------------------------------------------------------------------------
Some important limits.
---------------------------------------------------------------------------- -/

/-! #brief The limit of the empty diagram, if it exists, is final.
-/
@[reducible] definition EmptyCat.init.limit_final (C : Cat.{ℓobj₁ ℓhom₁})
    (fin : Limit (EmptyCat.init.{ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂} C))
    : Final C
:= let mcone : [[C]] → Cone (EmptyCat.init C)
            := λ c, { obj := c
                    , proj := λ x, pempty.elim x
                    , triangle := λ x₁ x₂ f, pempty.elim f
                    }
   in { obj := fin
      , final := λ c, Limit.mediate fin (mcone c)
      , uniq := λ c h, begin
                         apply Limit.mediate_uniq fin (mcone c),
                         intro e, apply pempty.elim e
                       end
      }

/-! #brief Every category with finite limits has a final object.
-/
@[reducible] definition HasAllFiniteLimits.HasFinal (C : Cat.{ℓobj₁ ℓhom₁})
    (C_HasAllFiniteLimits : HasAllFiniteLimits C)
    : Final C
:= EmptyCat.init.limit_final C
    (C_HasAllFiniteLimits EmptyCat.Fin (EmptyCat.init C))

end qp
