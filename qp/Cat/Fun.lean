/- ----------------------------------------------------------------------------
Functors.
---------------------------------------------------------------------------- -/

import .basic
universe variables ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂ ℓobj₃ ℓhom₃ ℓobj₄ ℓhom₄

namespace qp



/- ----------------------------------------------------------------------------
Composition of functors, revisited.
---------------------------------------------------------------------------- -/

/-! #brief Composition into the left-argument of a functor out of a product category.
-/
@[reducible] definition Fun.left_comp
    {C : Cat.{ℓobj₁ ℓhom₁}} {D₁ : Cat.{ℓobj₂ ℓhom₂}} {D₂ : Cat.{ℓobj₃ ℓhom₃}} {E : Cat.{ℓobj₄ ℓhom₄}}
    (G : C ⇉⇉ D₁) (F : D₁ ×× D₂ ⇉⇉ E)
    : C ×× D₂ ⇉⇉ E
:= { obj := λ x, F (pprod.mk (G x^.fst) x^.snd)
   , hom := λ x y f, F^.hom { fst := G ↗ f^.fst, snd := f^.snd }
   , hom_id := λ x, begin dsimp, simp, rw -F^.hom_id end
   , hom_circ := λ x y z g f, begin dsimp, rw -F^.hom_circ, rw G^.hom_circ end
   }

/-! #brief Composition into the right-argument of a functor out of a product category.
-/
@[reducible] definition Fun.right_comp
    {C : Cat.{ℓobj₁ ℓhom₁}} {D₁ : Cat.{ℓobj₂ ℓhom₂}} {D₂ : Cat.{ℓobj₃ ℓhom₃}} {E : Cat.{ℓobj₄ ℓhom₄}}
    (G : C ⇉⇉ D₂) (F : D₁ ×× D₂ ⇉⇉ E)
    : D₁ ×× C ⇉⇉ E
:= { obj := λ x, F (pprod.mk x^.fst (G x^.snd))
   , hom := λ x y f, F^.hom { fst := f^.fst, snd := G ↗ f^.snd }
   , hom_id := λ x, begin dsimp, simp, rw -F^.hom_id end
   , hom_circ := λ x y z g f, begin dsimp, rw -F^.hom_circ, rw G^.hom_circ end
   }

/-! #brief Filling the left-argument of a functor out of a product category.
-/
@[reducible] definition Fun.left_fill
    {C₁ : Cat.{ℓobj₁ ℓhom₁}} {C₂ : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    (F : C₁ ×× C₂ ⇉⇉ D)
    (c : [[C₁]])
    : C₂ ⇉⇉ D
:= { obj := λ x, F { fst := c, snd := x }
   , hom := λ x y f, F^.hom { fst := ⟨⟨c⟩⟩, snd := f }
   , hom_id := λ x, begin dsimp, rw -F^.hom_id end
   , hom_circ := λ x y z g f, begin dsimp, rw -F^.hom_circ, dsimp, simp end
   }

/-! #brief Filling the right-argument of a functor out of a product category.
-/
@[reducible] definition Fun.right_fill
    {C₁ : Cat.{ℓobj₁ ℓhom₁}} {C₂ : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    (F : C₁ ×× C₂ ⇉⇉ D)
    (c : [[C₂]])
    : C₁ ⇉⇉ D
:= { obj := λ x, F { fst := x, snd := c }
   , hom := λ x y f, F^.hom { fst := f, snd := ⟨⟨c⟩⟩ }
   , hom_id := λ x, begin dsimp, rw -F^.hom_id end
   , hom_circ := λ x y z g f, begin dsimp, rw -F^.hom_circ, dsimp, simp end
   }

end qp
