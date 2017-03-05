/- ----------------------------------------------------------------------------
Functors.
---------------------------------------------------------------------------- -/

import .basic
universe variables ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂ ℓobj₃ ℓhom₃ ℓobj₄ ℓhom₄

namespace qp



/- ----------------------------------------------------------------------------
Endo-functors.
---------------------------------------------------------------------------- -/

/-! #brief Iterated composition.
-/
definition Fun.iter_comp {C : Cat.{ℓobj₁ ℓhom₁}}
    (F : C ⇉⇉ C)
    : ℕ → C ⇉⇉ C
| 0 := Fun.id C
| (nat.succ n) := F □□ Fun.iter_comp n



/- ----------------------------------------------------------------------------
Functors and product categories.
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

/-! #brief Right product.
-/
@[reducible] definition LeftProdFun
    {C₁ : Cat.{ℓobj₁ ℓhom₁}} (c₁ : [[C₁]])
    (C₂ : Cat.{ℓobj₂ ℓhom₂})
    : C₂ ⇉⇉ C₁ ×× C₂
:= { obj := λ c₂, { fst := c₁, snd := c₂ }
   , hom := λ c₂₁ c₂₂ f₂, { fst := ⟨⟨c₁⟩⟩, snd := f₂ }
   , hom_id := λ x, rfl
   , hom_circ := λ x y z g f, begin dsimp, simp end
   }

/-! #brief Left product.
-/
@[reducible] definition RightProdFun
    (C₁ : Cat.{ℓobj₁ ℓhom₁})
    {C₂ : Cat.{ℓobj₂ ℓhom₂}} (c₂ : [[C₂]])
    : C₁ ⇉⇉ C₁ ×× C₂
:= { obj := λ c₁, { fst := c₁, snd := c₂ }
   , hom := λ c₁₁ c₁₂ f₁, { fst := f₁, snd := ⟨⟨c₂⟩⟩ }
   , hom_id := λ x, rfl
   , hom_circ := λ x y z g f, begin dsimp, simp end
   }

end qp
