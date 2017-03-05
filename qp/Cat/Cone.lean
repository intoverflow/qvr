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
   (hom : ∀ (x : [[B]]), obj →→ F x)
   (triangle : ∀ {x₁ x₂ : [[B]]} (f : x₁ →→ x₂)
               , hom x₂ = (F ↗ f) ∘∘ hom x₁)

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
             , c₁^.hom x = c₂^.hom x ∘∘ mediate)

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
definition ConeHom.id {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : B ⇉⇉ C} (c : Cone F)
    : ConeHom c c
:= { mediate := ⟨⟨c^.obj⟩⟩
   , factor := λ x, by simp
   }

@[simp] theorem ConeHom.id.simp_mediate {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : B ⇉⇉ C} (c : Cone F)
    : (ConeHom.id c)^.mediate = ⟨⟨c^.obj⟩⟩
:= rfl

/-! #brief Composition of ConeHoms.
-/
definition ConeHom.comp {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : B ⇉⇉ C} {c₁ c₂ c₃ : Cone F}
    (g : ConeHom c₂ c₃) (f : ConeHom c₁ c₂)
    : ConeHom c₁ c₃
:= { mediate := g^.mediate ∘∘ f^.mediate
   , factor
      := λ x
         , begin
             calc c₁^.hom x
                      = c₂^.hom x ∘∘ f^.mediate                 : f^.factor
                  ... = (c₃^.hom x ∘∘ g^.mediate) ∘∘ f^.mediate : begin rw [g^.factor], apply rfl end
                  ... = c₃^.hom x∘∘(g^.mediate∘∘f^.mediate)     : by rw C^.circ_assoc
           end
   }

@[simp] theorem ConeHom.comp.simp_mediate {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : B ⇉⇉ C} {c₁ c₂ c₃ : Cone F}
    (g : ConeHom c₂ c₃) (f : ConeHom c₁ c₂)
    : (ConeHom.comp g f)^.mediate = g^.mediate ∘∘ f^.mediate
:= rfl

/-! #brief Composition of ConeHoms is associative.
-/
theorem ConeHom.comp_assoc {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
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
:= begin
     apply ConeHom.eq,
     rw [ConeHom.comp.simp_mediate],
     rw [ConeHom.id.simp_mediate],
     apply C^.circ_id_left
   end

/-! #brief ConeHom.id is a right-identity for ConeHom.comp.
-/
@[simp] theorem ConeHom.comp_id_right {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : B ⇉⇉ C} {c₁ c₂ : Cone F}
    {f : ConeHom c₁ c₂}
    : ConeHom.comp f (ConeHom.id c₁) = f
:= begin
     apply ConeHom.eq,
     rw [ConeHom.comp.simp_mediate],
     rw [ConeHom.id.simp_mediate],
     apply Cat.circ_id_right
   end



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
definition Limit {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    (F : B ⇉⇉ C)
    : Type (max 1 ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂)
:= Final (ConeCat F)

local attribute [reducible] Limit

/-! #brief Helper for building a limit.
-/
definition Limit.mk {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    (F : B ⇉⇉ C)
    (c : [[C]])
    (proj : ∀ (x : [[B]]), c →→ F x)
    (univ : ∀ (cone : Cone F), C^.hom cone c)
    (ωtriangle : ∀ {x₁ x₂ : [[B]]} (f : x₁ →→ x₂), proj x₂ = (F ↗ f) ∘∘ proj x₁)
    (ωfactor : ∀ (cone : Cone F) {x : [[B]]}, cone^.hom x = proj x ∘∘ univ cone)
    (ωuniq : ∀ (cone : Cone F) (h : ConeHom cone (Cone.mk c proj @ωtriangle)), h^.mediate = univ cone)
    : Limit F
:= { obj := { obj := c
            , hom := proj
            , triangle := @ωtriangle
            }
   , hom := λ cone, { mediate := univ cone
                    , factor := @ωfactor cone
                    }
   , uniq := λ cone h, begin apply ConeHom.eq, apply ωuniq end
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
definition Limit.proj {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : B ⇉⇉ C}
    (c : Limit F)
    (x : [[B]])
    : C^.hom c (F x)
:= c^.obj^.hom x

/-! #brief Limit.proj satisfies the triangle equation.
-/
theorem Limit.proj.triangle {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : B ⇉⇉ C} (c : Limit F)
    {x₁ x₂ : [[B]]} (f : x₁ →→ x₂)
    : Limit.proj c x₂ = (F ↗ f) ∘∘ Limit.proj c x₁
:= c^.obj^.triangle f

/-! #brief The universal map (in C) from a cone to the limit.
-/
definition Limit.univ {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : B ⇉⇉ C}
    (c : Limit F) (c' : Cone F)
    : C^.hom c' c
:= c^.hom^.mediate

/-! #brief The universal map has the usual factoring property.
-/
theorem Limit.univ.factor {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : B ⇉⇉ C}
    (c : Limit F) (c' : Cone F)
    {x : [[B]]}
    : c'^.hom x = c^.proj x ∘∘ c^.univ c'
  := by apply ConeHom.factor

/-! #brief The universal map is unique among maps which factor.
-/
theorem Limit.univ.uniq {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : B ⇉⇉ C}
    (c : Limit F) (c' : Cone F)
    {f : C^.hom c' c}
    (ωf : ∀ {x : [[B]]}, c'^.hom x = c^.proj x ∘∘ f)
    : f = Limit.univ c c'
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
definition Limit.Iso {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : B ⇉⇉ C}
    (c₁ c₂ : Limit F)
    : Iso (c₂^.univ c₁)
          (c₁^.univ c₂)
:= let iso := Final.Iso c₁ c₂
   in { id₁ := congr_arg ConeHom.mediate iso^.id₁
      , id₂ := congr_arg ConeHom.mediate iso^.id₂
      }



/- ----------------------------------------------------------------------------
Categories with limits.
---------------------------------------------------------------------------- -/

/-! #brief Existence of a limit in a category.
-/
class HasLimit {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    (F : B ⇉⇉ C)
    : Type (max 1 ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂)
:= (limit : Limit F)

/-! #brief The limit of a functor.
-/
definition limit {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    (F : B ⇉⇉ C)
    [F_HasLimit : HasLimit F]
    : Limit F
:= HasLimit.limit F


/-! #brief A category with all limits of a given shape.
-/
class HasAllLimitsOfShape (C : Cat.{ℓobj₂ ℓhom₂})
    (B : Cat.{ℓobj₁ ℓhom₁})
    : Type (max ((max ℓobj₁ ℓhom₁) + 1) ℓobj₂ ℓhom₂)
:= (limit : ∀ (F : B ⇉⇉ C), HasLimit F)

attribute [instance] HasAllLimitsOfShape.limit

/-! #brief A category with all limits.
-/
class HasAllLimits
    (C : Cat.{ℓobj₂ ℓhom₂})
    : Type (max ((max ℓobj₁ ℓhom₁) + 1) ℓobj₂ ℓhom₂)
:= (limit : ∀ (B : Cat.{ℓobj₁ ℓhom₁}), HasAllLimitsOfShape C B)

attribute [instance] HasAllLimits.limit

/-! #brief A category with all finite limits.
-/
class HasAllFiniteLimits
    (C : Cat.{ℓobj₂ ℓhom₂})
    : Type (max ((max ℓobj₁ ℓhom₁) + 1) ℓobj₂ ℓhom₂)
:= (limit : ∀ {B : Cat.{ℓobj₁ ℓhom₁}}
              [B_Fin : Cat.Fin B]
            , HasAllLimitsOfShape C B)

attribute [instance] HasAllFiniteLimits.limit

/-! #brief Categories with all limits have all finite limits.
-/
instance HasAllLimits.HasAllFiniteLimits (C : Cat.{ℓobj₂ ℓhom₂})
    [C_HasAllLimits : HasAllLimits.{ℓobj₁ ℓobj₂} C]
    : HasAllFiniteLimits.{ℓobj₁ ℓobj₂} C
:= { limit := λ B B_Fin, HasAllLimits.limit C B }



/- ----------------------------------------------------------------------------
Preservation of limits by functors.
---------------------------------------------------------------------------- -/

-- Notion of when a functor preserves a limit.
class PreservesLimit {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    (F : C ⇉⇉ D)
    {B : Cat.{ℓobj₁ ℓhom₁}}
    (J : B ⇉⇉ C)
    [J_HasLimit : HasLimit J]
    : Type ((max ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂ ℓobj₃ ℓhom₃) + 1)
:= (preserves : HasLimit (F □□ J))
   (preserves_eq : (@limit _ _ _ preserves)^.obj^.obj = F (limit J))

attribute [instance] PreservesLimit.preserves

/-! #brief A functor which preserves limits of a given shape.
-/
class PreservesLimitsOfShape {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    (F : C ⇉⇉ D)
    (B : Cat.{ℓobj₁ ℓhom₁})
:= (preserves : ∀ (J : B ⇉⇉ C) [J_HasLimit : HasLimit J], PreservesLimit F J)

attribute [instance] PreservesLimitsOfShape.preserves


/- ----------------------------------------------------------------------------
Final objects as limits.
---------------------------------------------------------------------------- -/

/-! #brief The limit of the empty diagram, if it exists, is final.
-/
@[reducible] definition EmptyCat.init.limit_final (C : Cat.{ℓobj₁ ℓhom₁})
    (fin : Limit (EmptyCat.init.{ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂} C))
    : Final C
:= let mcone : [[C]] → Cone (EmptyCat.init C)
            := λ c, { obj := c
                    , hom := λ x, pempty.elim x
                    , triangle := λ x₁ x₂ f, pempty.elim f
                    }
   in { obj := fin
      , hom := λ c, fin^.univ (mcone c)
      , uniq := λ c h, begin
                         apply fin^.univ.uniq (mcone c),
                         intro e, apply pempty.elim e
                       end
      }

/-! #brief A category with limits out of EmptyCat has a final object.
-/
instance HasAllFiniteLimits.HasFinal
    (C : Cat.{ℓobj₂ ℓhom₂})
    [C_HasAllLimitsOfShape_Empty : HasAllLimitsOfShape C EmptyCat]
    : HasFinal C
:= { final := EmptyCat.init.limit_final C (limit (EmptyCat.init C))
   }



/- ----------------------------------------------------------------------------
Co-limits.
---------------------------------------------------------------------------- -/

/-! #brief A co-limit of a functor.
-/
definition CoLimit {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    (F : B ⇉⇉ C)
    : Type (max 1 ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂)
:= Limit (OpFun F)

local attribute [reducible] CoLimit

/-! #brief Helper for building a limit.
-/
definition CoLimit.mk {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    (F : B ⇉⇉ C)
    (c : [[C]])
    (incl : ∀ (x : [[B]]), F x →→ c)
    (univ : ∀ (cone : Cone (OpFun F)), C^.hom c cone)
    (ωtriangle : ∀ {x₁ x₂ : [[B]]} (f : x₂ →→ x₁), incl x₂ = incl x₁ ∘∘ (F ↗ f))
    (ωfactor : ∀ (cone : Cone (OpFun F)) {x : [[B]]}, cone^.hom x = univ cone ∘∘ incl x)
    (ωuniq : ∀ (cone : Cone (OpFun F)) (h : ConeHom cone (Cone.mk c incl @ωtriangle)), h^.mediate = univ cone)
    : CoLimit F
:= Limit.mk (OpFun F) c incl univ @ωtriangle ωfactor ωuniq

/-! #brief Every co-limit can be used as an object.
-/
@[reducible] instance CoLimit.has_coe_to_obj {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    (F : B ⇉⇉ C)
    : has_coe (CoLimit F) [[C]]
:= { coe := λ x, by apply x^.obj^.obj
   }

/-! #brief The map to the co-limit from the image of the diagram.
-/
definition CoLimit.incl {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : B ⇉⇉ C}
    (c : CoLimit F)
    (x : [[B]])
    : C^.hom (F x) c
:= Limit.proj c x

/-! #brief CoLimit.incl satisfies the triangle equation.
-/
theorem CoLimit.incl.triangle {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : B ⇉⇉ C} (c : CoLimit F)
    {x₁ x₂ : [[B]]} (f : x₂ →→ x₁)
    : CoLimit.incl c x₂ = CoLimit.incl c x₁ ∘∘ (F ↗ f)
:= Limit.proj.triangle c f

/-! #brief The universal map (in C) from a co-limit to a cone.
-/
definition CoLimit.univ {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : B ⇉⇉ C}
    (c : CoLimit F) (c' : Cone (OpFun F))
    : C^.hom c c'
:= Limit.univ c c'

/-! #brief The universal map has the usual factoring property.
-/
theorem CoLimit.univ.factor {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : B ⇉⇉ C}
    (c : CoLimit F) (c' : Cone (OpFun F))
    {x : [[B]]}
    : c'^.hom x = c^.univ c' ∘∘ c^.proj x
:= Limit.univ.factor c c'

/-! #brief The universal map is unique among maps which factor.
-/
theorem CoLimit.univ.uniq {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : B ⇉⇉ C}
    (c : CoLimit F) (c' : Cone (OpFun F))
    {f : C^.hom c c'}
    (ωf : ∀ {x : [[B]]}, c'^.hom x = f ∘∘ c^.proj x)
    : f = CoLimit.univ c c'
:= Limit.univ.uniq c c' @ωf

/-! #brief Limits are unique up to isomorphism.
-/
definition CoLimit.Iso {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : B ⇉⇉ C}
    (c₁ c₂ : CoLimit F)
    : Iso (c₁^.univ c₂)
          (c₂^.univ c₁)
:= { id₁ := by apply (Limit.Iso c₂ c₁)^.id₂
   , id₂ := by apply (Limit.Iso c₂ c₁)^.id₁
   }



/- ----------------------------------------------------------------------------
Categories with co-limits.
---------------------------------------------------------------------------- -/

/-! #brief Existence of a co-limit in a category.
-/
class HasCoLimit {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    (F : B ⇉⇉ C)
    : Type (max 1 ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂)
:= (colimit : CoLimit F)

/-! #brief The co-limit of a functor.
-/
definition colimit {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    (F : B ⇉⇉ C)
    [F_HasCoLimit : HasCoLimit F]
    : CoLimit F
:= HasCoLimit.colimit F

/-! #brief The universal map out of the co-limit.
-/
definition colimit.univ {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    (F : B ⇉⇉ C)
    [F_HasCoLimit : HasCoLimit F]
    (c : Cone (OpFun F))
    : C^.hom (colimit F) c
:= CoLimit.univ (colimit F) c


/-! #brief A category with all co-limits of a given shape.
-/
class HasAllCoLimitsOfShape (C : Cat.{ℓobj₂ ℓhom₂})
    (B : Cat.{ℓobj₁ ℓhom₁})
    : Type (max ((max ℓobj₁ ℓhom₁) + 1) ℓobj₂ ℓhom₂)
:= (colimit : ∀ (F : B ⇉⇉ C), HasCoLimit F)

attribute [instance] HasAllCoLimitsOfShape.colimit

/-! #brief A category with all co-limits.
-/
class HasAllCoLimits
    (C : Cat.{ℓobj₂ ℓhom₂})
    : Type (max ((max ℓobj₁ ℓhom₁) + 1) ℓobj₂ ℓhom₂)
:= (colimit : ∀ (B : Cat.{ℓobj₁ ℓhom₁}), HasAllCoLimitsOfShape C B)

attribute [instance] HasAllCoLimits.colimit

/-! #brief A category with all finite co-limits.
-/
class HasAllFiniteCoLimits
    (C : Cat.{ℓobj₂ ℓhom₂})
    : Type (max ((max ℓobj₁ ℓhom₁) + 1) ℓobj₂ ℓhom₂)
:= (colimit : ∀ {B : Cat.{ℓobj₁ ℓhom₁}}
                [B_Fin : Cat.Fin B]
              , HasAllCoLimitsOfShape C B)

attribute [instance] HasAllFiniteCoLimits.colimit

/-! #brief Categories with all co-limits have all finite co-limits.
-/
instance HasAllCoLimits.HasAllFiniteCoLimits (C : Cat.{ℓobj₂ ℓhom₂})
    [C_HasAllCoLimits : HasAllCoLimits.{ℓobj₁ ℓobj₂} C]
    : HasAllFiniteCoLimits.{ℓobj₁ ℓobj₂} C
:= { colimit := λ B B_Fin, HasAllCoLimits.colimit C B }



/- ----------------------------------------------------------------------------
Preservation of co-limits by functors.
---------------------------------------------------------------------------- -/

-- Notion of when a functor preserves a co-limit.
class PreservesCoLimit {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    (F : C ⇉⇉ D)
    {B : Cat.{ℓobj₁ ℓhom₁}}
    (J : B ⇉⇉ C)
    : Type ((max ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂ ℓobj₃ ℓhom₃) + 1)
:= (colimit : ∀ [J_HasCoLimit : HasCoLimit J], HasCoLimit (F □□ J))
   (colimit_in : ∀ [J_HasCoLimit : HasCoLimit J], ↑(@qp.colimit _ _ _ colimit) →→ F (qp.colimit J))
   (colimit_out : ∀ [J_HasCoLimit : HasCoLimit J], F (qp.colimit J) →→ ↑(@qp.colimit _ _ _ colimit))
   (iso : ∀ [J_HasCoLimit : HasCoLimit J], Iso colimit_out colimit_in)

attribute [instance] PreservesCoLimit.colimit

definition colimit.preserves.in {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    (F : C ⇉⇉ D)
    {B : Cat.{ℓobj₁ ℓhom₁}}
    (J : B ⇉⇉ C)
    [J_HasCoLimit : HasCoLimit J]
    [F_PreservesCoLimit_J : PreservesCoLimit F J]
    : ↑(colimit (F □□ J)) →→ F ↑(colimit J)
:= PreservesCoLimit.colimit_in F J

definition colimit.preserves.out {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    (F : C ⇉⇉ D)
    {B : Cat.{ℓobj₁ ℓhom₁}}
    (J : B ⇉⇉ C)
    [J_HasCoLimit : HasCoLimit J]
    [F_PreservesCoLimit_J : PreservesCoLimit F J]
    : F ↑(colimit J) →→ ↑(colimit (F □□ J))
:= PreservesCoLimit.colimit_out F J

definition colimit.preserves.Iso {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    (F : C ⇉⇉ D)
    {B : Cat.{ℓobj₁ ℓhom₁}}
    (J : B ⇉⇉ C)
    [J_HasCoLimit : HasCoLimit J]
    [F_PreservesCoLimit_J : PreservesCoLimit F J]
    : Iso (colimit.preserves.out F J) (colimit.preserves.in F J)
:= PreservesCoLimit.iso F J

/-! #brief A functor which preserves co-limits of a given shape.
-/
class PreservesCoLimitsOfShape {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    (F : C ⇉⇉ D)
    (B : Cat.{ℓobj₁ ℓhom₁})
:= (preserves : ∀ (J : B ⇉⇉ C) [J_HasCoLimit : HasCoLimit J], PreservesCoLimit F J)

attribute [instance] PreservesLimitsOfShape.preserves



/- ----------------------------------------------------------------------------
Initial objects as co-limits.
---------------------------------------------------------------------------- -/

/-! #brief The co-limit of the empty diagram, if it exists, is initial.
-/
@[reducible] definition EmptyCat.init.colimit_init (C : Cat.{ℓobj₁ ℓhom₁})
    (ini : CoLimit (EmptyCat.init.{ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂} C))
    : Init C
:= let mcone : [[C]] → Cone (OpFun (EmptyCat.init C))
            := λ c, { obj := c
                    , hom := λ x, pempty.elim x
                    , triangle := λ x₁ x₂ f, pempty.elim f
                    }
   in { obj := ini
      , hom := λ c, ini^.univ (mcone c)
      , uniq := λ c h, begin
                         apply ini^.univ.uniq (mcone c),
                         intro e, apply pempty.elim e
                       end
      }

/-! #brief A category with co-limits out of EmptyCat has an initial object.
-/
instance HasAllFiniteCoLimits.HasInit
    (C : Cat.{ℓobj₂ ℓhom₂})
    [C_HasAllCoLimitsOfShape_Empty : HasAllCoLimitsOfShape C EmptyCat]
    : HasInit C
:= { init := EmptyCat.init.colimit_init C (colimit (EmptyCat.init C))
   }

end qp
