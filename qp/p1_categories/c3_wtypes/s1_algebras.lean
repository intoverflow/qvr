/- -----------------------------------------------------------------------
Algebras for endofunctors.
----------------------------------------------------------------------- -/

import ..c1_basic

namespace qp

open stdaux

universe variables ℓobj ℓhom



/- -----------------------------------------------------------------------
The category of algebras for an endofunctor.
----------------------------------------------------------------------- -/

/-! #brief An algebra for an endofunctor.
-/
structure EndoAlg {C : Cat.{ℓobj ℓhom}} (F : Fun C C)
    : Type (max ℓobj ℓhom)
:= (carr : C^.obj)
   (hom : C^.hom (F^.obj carr) carr)

/-! #brief Helper for proving equality of EndoAlg.
-/
theorem EndoAlg.eq {C : Cat.{ℓobj ℓhom}} {F : Fun C C}
    : ∀ {X₁ X₂ : EndoAlg F}
        (ωcarr : X₁^.carr = X₂^.carr)
        (ωhom : (X₁^.carr = X₂^.carr) → X₁^.hom == X₂^.hom)
      , X₁ = X₂
| (EndoAlg.mk carr hom₁) (EndoAlg.mk .(carr) hom₂)
  (eq.refl .(carr)) ωhom
:= begin
     assert ωhom' : hom₁ = hom₂,
     { apply eq_of_heq, exact ωhom rfl },
     subst ωhom'
   end

/-! #brief An algebra homomorphism for an endofunctor.
-/
structure EndoAlgHom {C : Cat.{ℓobj ℓhom}} (F : Fun C C)
    (X Y : EndoAlg F)
    : Type (max ℓobj ℓhom)
:= (hom : C^.hom X^.carr Y^.carr)
   (comm : C^.circ Y^.hom (F^.hom hom) = C^.circ hom X^.hom)

/-! #brief A helper for proving two homomorphisms are equal.
-/
theorem EndoAlgHom.eq {C : Cat.{ℓobj ℓhom}} {F : Fun C C}
    {X Y : EndoAlg F}
    : ∀ {F₁ F₂ : EndoAlgHom F X Y}
        (ω : F₁^.hom = F₂^.hom)
      , F₁ = F₂
| (EndoAlgHom.mk hom comm₁) (EndoAlgHom.mk .(hom) comm₂) (eq.refl .(hom))
:= rfl

/-! #brief The identity homomorphism.
-/
definition EndoAlgHom.id {C : Cat.{ℓobj ℓhom}} (F : Fun C C)
    (X : EndoAlg F)
    : EndoAlgHom F X X
:= { hom := C^.id X^.carr
   , comm := by rw [F^.hom_id, C^.circ_id_right, C^.circ_id_left]
   }

/-! #brief The composition of two homomorphisms.
-/
definition EndoAlgHom.comp {C : Cat.{ℓobj ℓhom}} (F : Fun C C)
    {X Y Z : EndoAlg F}
    (g : EndoAlgHom F Y Z)
    (f : EndoAlgHom F X Y)
    : EndoAlgHom F X Z
:= { hom := C^.circ g^.hom f^.hom
   , comm
      := begin
           rw [-C^.circ_assoc, -f^.comm],
           rw [C^.circ_assoc, -g^.comm],
           rw [-C^.circ_assoc, F^.hom_circ]
         end
   }

/-! #brief The category of algebras for an endofunctor.
-/
definition EndoAlgCat {C : Cat.{ℓobj ℓhom}} (F : Fun C C)
    : Cat
:= { obj := EndoAlg F
   , hom := EndoAlgHom F
   , id := EndoAlgHom.id F
   , circ := @EndoAlgHom.comp C F
   , circ_assoc := λ X Y Z W h g f, EndoAlgHom.eq C^.circ_assoc
   , circ_id_left := λ X Y f, EndoAlgHom.eq C^.circ_id_left
   , circ_id_right := λ X Y f, EndoAlgHom.eq C^.circ_id_right
   }

/-! #brief Initial objects in EndoAlgCat are special.
-/
@[class] definition HasInitAlg {C : Cat.{ℓobj ℓhom}} (F : Fun C C)
:= HasInit (EndoAlgCat F)

/-! #brief The carrier of an initial algebra.
-/
definition initalg.carr {C : Cat.{ℓobj ℓhom}} (F : Fun C C)
    [F_HasInitAlg : HasInitAlg F]
    : C^.obj
:= (@init _ F_HasInitAlg)^.carr

end qp
