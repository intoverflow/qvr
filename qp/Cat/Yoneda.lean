/- ----------------------------------------------------------------------------
The Yoneda embedding and the Yoneda lemma.
---------------------------------------------------------------------------- -/

import .basic

namespace qp
universe variables ℓobj ℓhom ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂ ℓobj₃ ℓhom₃ ℓobj₄ ℓhom₄



/- ----------------------------------------------------------------------------
The Yoneda embedding.
---------------------------------------------------------------------------- -/

/-! #brief The Yoneda embedding of a category into its presheaf category.
-/
@[reducible] definition YonedaFun (C : Cat.{ℓobj ℓhom})
    : C ⇉⇉ PreShCat C
:= { obj := λ c, { obj := λ x, x →→ c
                 , hom := λ x y f g, g ∘∘ f
                 , hom_id := λ x , begin apply funext, intro f, dsimp, simp end
                 , hom_circ := λ x y z g f, begin apply funext, intro h, dsimp, simp end
                 }
   , hom := λ x y g, { component := λ x f, g ∘∘ f
                     , transport := λ x y g, begin dsimp, apply funext, intro f, simp end
                     }
   , hom_id := λ x, begin apply NatTrans.eq, dsimp, intro y, apply funext, intro g, simp end
   , hom_circ := λ x y z g f, begin apply NatTrans.eq, dsimp, intro w, apply funext, intro h, simp end
   }

/-! #brief The Yoneda representation of a natural transformation.
-/
@[reducible] definition YonedaFun.represent {C : Cat.{ℓobj ℓhom}}
    (X : [[PreShCat C]])
    (c : [[C]])
    (η : YonedaFun C c ↣↣ X)
    : X c
:= η c ⟨⟨c⟩⟩

/-! #brief The natural transformation induced by a Yoneda representation.
-/
@[reducible] definition YonedaFun.construct {C : Cat.{ℓobj ℓhom}}
    (X : [[PreShCat C]])
    (c : [[C]])
    (r : X c)
    : YonedaFun C c ↣↣ X
:= { component := λ x g, (X ↗ g) r
   , transport := λ x y g, begin apply funext, intro f, dsimp, rw X^.hom_circ end
   }

/-! #brief YonedaFun.represent and YonedaFun.construct are inverses of one another.
-/
@[simp] theorem YonedaFun.represent_construct {C : Cat.{ℓobj ℓhom}}
    (X : [[PreShCat C]])
    (c : [[C]])
    (r : X c)
    : YonedaFun.represent X c (YonedaFun.construct X c r) = r
:= begin dsimp, rw X^.hom_id end

/-! #brief YonedaFun.construct and YonedaFun.represent are inverses of one another.
-/
@[simp] theorem YonedaFun.construct_represent {C : Cat.{ℓobj ℓhom}}
    (X : [[PreShCat C]])
    (c : [[C]])
    (η : YonedaFun C c ↣↣ X)
    : YonedaFun.construct X c (YonedaFun.represent X c η) = η
:= begin
     apply NatTrans.eq, intro y,
     dsimp,
     apply funext, intro g,
     assert lem₁ : η y g = η y (⟨⟨c⟩⟩ ∘∘ g),
     { rw Cat.circ_id_left },
     refine eq.symm (eq.trans lem₁ _),
     apply congr_fun η^.transport
   end

end qp
