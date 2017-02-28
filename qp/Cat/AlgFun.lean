/- ----------------------------------------------------------------------------
Algebras of endo-functors.
---------------------------------------------------------------------------- -/

import .basic
universe variables ℓobj ℓhom

namespace qp



/- ----------------------------------------------------------------------------
Algebras of endo-functors.
---------------------------------------------------------------------------- -/

-- An algebra of an endofunctor.
structure AlgFun {C : Cat.{ℓobj ℓhom}} (F : C ⇉⇉ C)
    : Type (max ℓobj ℓhom)
:= (obj : [[C]])
   (carrier : F obj →→ obj)

-- An hom of an algebra of an endofunctor.
structure AlgFunHom {C : Cat.{ℓobj ℓhom}} {F : C ⇉⇉ C}
    (X Y : AlgFun F)
    : Type (max ℓobj ℓhom)
:= (hom : X^.obj →→ Y^.obj)
   (square : hom ∘∘ X^.carrier = Y^.carrier ∘∘ (F^.hom hom))

/-! #brief An helper for proving equality of algebra homs.
-/
theorem AlgFunHom.eq {C : Cat.{ℓobj ℓhom}} {F : C ⇉⇉ C}
    {X Y : AlgFun F}
    : ∀ {f₁ f₂ : AlgFunHom X Y}
      , f₁^.hom = f₂^.hom
      → f₁ = f₂
| (AlgFunHom.mk f ω₁) (AlgFunHom.mk .f ω₂) (eq.refl .f) := rfl

/-! #brief The identity algebra hom.
-/
@[reducible] definition AlgFunHom.id {C : Cat.{ℓobj ℓhom}} {F : C ⇉⇉ C}
    (X : AlgFun F)
    : AlgFunHom X X
:= { hom := ⟨⟨X^.obj⟩⟩
   , square := by simp
   }

/-! #brief Composition of algebra homs.
-/
@[reducible] definition AlgFunHom.comp {C : Cat.{ℓobj ℓhom}} {F : C ⇉⇉ C}
    {X Y Z : AlgFun F} (g : AlgFunHom Y Z) (f : AlgFunHom X Y)
    : AlgFunHom X Z
:= { hom := g^.hom ∘∘ f^.hom
   , square := begin
                 rw -C^.circ_assoc,
                 rw f^.square,
                 rw C^.circ_assoc,
                 rw g^.square,
                 rw F^.hom_circ,
                 rw C^.circ_assoc
               end
   }

/-! #brief The category of algebras of an endofunctor.
-/
@[reducible] definition AlgFunCat {C : Cat.{ℓobj ℓhom}}
    (F : C ⇉⇉ C)
    : Cat.{(max ℓobj ℓhom) ((max ℓobj ℓhom) + 1)}
:= { obj := AlgFun F
   , hom := AlgFunHom
   , id := @AlgFunHom.id C F
   , circ := @AlgFunHom.comp C F
   , circ_assoc := λ x y z w h g f, begin apply AlgFunHom.eq, apply C^.circ_assoc end
   , circ_id_left := λ x y f, begin apply AlgFunHom.eq, simp end
   , circ_id_right := λ x y f, begin apply AlgFunHom.eq, simp end
   }

end qp
