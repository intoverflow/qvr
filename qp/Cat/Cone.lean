/- ----------------------------------------------------------------------------
Cones and cocones.
---------------------------------------------------------------------------- -/

import .basic

namespace qp
universe variables ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂ ℓobj₃ ℓhom₃



/- ----------------------------------------------------------------------------
Cones.
---------------------------------------------------------------------------- -/

-- A cone of a functor.
structure IsCone
    {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    (F : B ⇉⇉ C)
    (c : [[C]])
    : Type  ((max ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂) + 1)
:= (proj : ∀ (x : [[B]]), c →→ F x)
   (proj_circ : ∀ {x₁ x₂ : [[B]]} (f : x₁ →→ x₂)
                , proj x₂ = (F ↗ f) ∘∘ proj x₁)

-- Boxed version of IsCone.
structure HasCone {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    (F : B ⇉⇉ C)
    : Type ((max ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂) + 1)
:= (cone : [[C]])
   (is_cone : IsCone F cone)

-- A homomorphism between cones.
structure ConeHom {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : B ⇉⇉ C}
    {c₁ : [[C]]} (cone₁ : IsCone F c₁)
    {c₂ : [[C]]} (cone₂ : IsCone F c₂)
    : Type ((max ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂) + 1)
:= (mediate : c₁ →→ c₂)
   (factor : ∀ {x : [[B]]}
             , IsCone.proj cone₁ x = IsCone.proj cone₂ x ∘∘ mediate)

-- TODO: Fix docstring!
--/-! #brief Every cone can be treated as a function on objects.
---/
@[reducible] instance IsCone.has_coe_to_fun {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : B ⇉⇉ C}
    {c : [[C]]}
    : has_coe_to_fun (IsCone F c)
:= { F := λ is_cone, ∀ (x : [[B]]), c →→ F x
   , coe := IsCone.proj
   }

/-! #brief Every IsCone can be used as a HasCone.
-/
@[reducible] instance IsCone.has_coe_to_HasCone {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : B ⇉⇉ C}
    {c : [[C]]}
    : has_coe (IsCone F c) (HasCone F)
:= { coe := HasCone.mk c
   }

/-! #brief Every HasCone can be used as an object.
-/
@[reducible] instance HasCone.has_coe_to_obj {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : B ⇉⇉ C}
    : has_coe (HasCone F) [[C]]
:= { coe := HasCone.cone
   }

--/-! #brief Every HasCone can be treated as a function on objects.
---/
@[reducible] instance HasCone.has_coe_to_fun {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : B ⇉⇉ C}
    : has_coe_to_fun (HasCone F)
:= { F := λ has_cone, ∀ (x : [[B]]), has_cone^.cone →→ F x
   , coe := λ has_cone, has_cone^.is_cone^.proj
   }

/-! #brief Every ConeHom can be used as a hom.
-/
@[reducible] instance ConeHom.has_coe_to_hom {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : B ⇉⇉ C}
    {c₁ : [[C]]} (cone₁ : IsCone F c₁)
    {c₂ : [[C]]} (cone₂ : IsCone F c₂)
    : has_coe (ConeHom cone₁ cone₂) (c₁ →→ c₂)
:= { coe := ConeHom.mediate
   }

/-! #brief Helper lemma for proving quality of ConeHoms.
-/
theorem ConeHom.eq {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : B ⇉⇉ C}
    {c₁ : [[C]]} (cone₁ : IsCone F c₁)
    {c₂ : [[C]]} (cone₂ : IsCone F c₂)
    : ∀ (h₁ h₂ : ConeHom cone₁ cone₂)
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
    {F : B ⇉⇉ C}
    {c : [[C]]} (cone : IsCone F c)
    : ConeHom cone cone
:= { mediate := ⟨⟨c⟩⟩
   , factor := λ x, by simp
   }

/-! #brief Composition of ConeHoms.
-/
@[reducible] definition ConeHom.comp {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : B ⇉⇉ C}
    {c₁ : [[C]]} {cone₁ : IsCone F c₁}
    {c₂ : [[C]]} {cone₂ : IsCone F c₂}
    {c₃ : [[C]]} {cone₃ : IsCone F c₃}
    (g : ConeHom cone₂ cone₃) (f : ConeHom cone₁ cone₂)
    : ConeHom cone₁ cone₃
:= { mediate := g^.mediate ∘∘ f^.mediate
   , factor := λ x, begin simp, rw -g^.factor, apply f^.factor end
   }

/-! #brief Composition of ConeHoms is associative.
-/
@[simp] theorem ConeHom.comp_assoc {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : B ⇉⇉ C}
    {c₁ : [[C]]} {cone₁ : IsCone F c₁}
    {c₂ : [[C]]} {cone₂ : IsCone F c₂}
    {c₃ : [[C]]} {cone₃ : IsCone F c₃}
    {c₄ : [[C]]} {cone₄ : IsCone F c₄}
    {h : ConeHom cone₃ cone₄} {g : ConeHom cone₂ cone₃} {f : ConeHom cone₁ cone₂}
    : ConeHom.comp h (ConeHom.comp g f) = ConeHom.comp (ConeHom.comp h g) f
:= begin apply ConeHom.eq, simp end

/-! #brief ConeHom.id is a left-identity for ConeHom.comp.
-/
@[simp] theorem ConeHom.comp_id_left {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : B ⇉⇉ C}
    {c₁ : [[C]]} {cone₁ : IsCone F c₁}
    {c₂ : [[C]]} {cone₂ : IsCone F c₂}
    {f : ConeHom cone₁ cone₂}
    : ConeHom.comp (ConeHom.id cone₂) f = f
:= begin apply ConeHom.eq, simp end

/-! #brief ConeHom.id is a right-identity for ConeHom.comp.
-/
@[simp] theorem ConeHom.comp_id_right {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : B ⇉⇉ C}
    {c₁ : [[C]]} {cone₁ : IsCone F c₁}
    {c₂ : [[C]]} {cone₂ : IsCone F c₂}
    {f : ConeHom cone₁ cone₂}
    : ConeHom.comp f (ConeHom.id cone₁) = f
:= begin apply ConeHom.eq, simp end



/- ----------------------------------------------------------------------------
The category of cones.
---------------------------------------------------------------------------- -/

/-! #brief The category of cones.
-/
@[reducible] definition ConeCat {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    (F : B ⇉⇉ C)
    : Cat
:= { obj := HasCone F
   , hom := λ cone₁ cone₂, ConeHom cone₁^.is_cone cone₂^.is_cone
   , id := λ cone, ConeHom.id cone^.is_cone
   , circ := λ cone₁ cone₂ cone₃, ConeHom.comp
   , circ_assoc := λ cone₁ cone₂ cone₃ cone₄ h g f, ConeHom.comp_assoc
   , circ_id_left := λ cone₁ cone₂ f, ConeHom.comp_id_left
   , circ_id_right := λ cone₁ cone₂ f, ConeHom.comp_id_right
   }

/-! #brief Every object in ConeCat can be used as an object in the codomain.
-/
@[reducible] instance ConeCat.obj_has_coe_to_obj {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : B ⇉⇉ C}
    : has_coe [[ConeCat F]] [[C]]
:= { coe := HasCone.cone
   }

--/-! #brief Every object in ConeCat can be treated as a function on objects of the domain.
---/
@[reducible] instance ConeCat.obj_has_coe_to_fun {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : B ⇉⇉ C}
    : has_coe_to_fun [[ConeCat F]]
:= { F := λ has_cone, ∀ (x : [[B]]), has_cone^.cone →→ F x
   , coe := λ has_cone, has_cone^.is_cone^.proj
   }

/-! #brief Every hom in ConeCat can be used as a hom in the codomain.
-/
@[reducible] instance ConeCat.hom_has_coe_to_hom {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : B ⇉⇉ C}
    {cone₁ cone₂ : [[ConeCat F]]}
    : has_coe ((ConeCat F)^.hom cone₁ cone₂) (C^.hom cone₁ cone₂)
:= { coe := ConeHom.mediate
   }



/- ----------------------------------------------------------------------------
Limits.
---------------------------------------------------------------------------- -/

-- A limit of a functor.
structure IsLimit {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    (F : B ⇉⇉ C)
    (c : [[C]])
    : Type ((max ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂) + 1)
:= (is_cone : IsCone F c)
   (is_final : IsFinal (ConeCat F) (HasCone.mk c is_cone))

-- Notion of when a functor preserves limits.
structure PreservesLimits {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    (F : C ⇉⇉ D)
    : Type ((max ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂ ℓobj₃ ℓhom₃) + 1)
:= (limit : ∀ {B : Cat.{ℓobj₁ ℓhom₁}} (D : Fun B C)
              (c : [[C]])
              (c_limit : IsLimit D c)
            , IsLimit (F □□ D) (F c))

-- A witness that a category has all limits.
structure HasAllLimits
    (C : Cat.{ℓobj₂ ℓhom₂})
    : Type ((max ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂) + 1)
:= (limit : ∀ {B : Cat.{ℓobj₁ ℓhom₁}}
              (F : B ⇉⇉ C)
            , [[C]])
   (is_limit : ∀ {B : Cat.{ℓobj₁ ℓhom₁}}
                 (F : B ⇉⇉ C)
               , IsLimit F (limit F))

end qp
