/- ----------------------------------------------------------------------------
Monoidal categories.
---------------------------------------------------------------------------- -/

import .basic
import .Fun
import .Product

namespace qp
universe variables ℓobj ℓhom



-- A monoidal category.
structure Monoidal (C : Cat.{ℓobj ℓhom})
    : Type ((max ℓobj ℓhom) + 1)
:= (tensor : C ×× C ⇉⇉ C)
   (unit : [[C]])
   (assoc_left : Fun.right_comp tensor tensor ↣↣ Fun.left_comp tensor tensor □□ ProdCat.assoc_left)
   (assoc_right : Fun.left_comp tensor tensor □□ ProdCat.assoc_left ↣↣ Fun.right_comp tensor tensor)
   (assoc_iso : NatIso assoc_left assoc_right)
   (left_unitor : Fun.left_fill tensor unit ↣↣ Fun.id C)
   (left_unitor_inv : Fun.id C ↣↣ Fun.left_fill tensor unit)
   (left_unitor_iso : NatIso left_unitor left_unitor_inv)
   (right_unitor : Fun.right_fill tensor unit ↣↣ Fun.id C)
   (right_unitor_inv : Fun.id C ↣↣ Fun.right_fill tensor unit)
   (right_unitor_iso : NatIso right_unitor right_unitor_inv)
   (triangle : ∀ {x y : [[C]]}
               , let lefty : tensor ⟨x, tensor ⟨unit, y⟩ ⟩ →→ tensor ⟨x, y⟩
                      := tensor^.hom ⟨ ⟨⟨x⟩⟩, left_unitor y ⟩
                 in lefty ∘∘ assoc_right ⟨x, unit, y⟩ = tensor^.hom ⟨ right_unitor x, ⟨⟨y⟩⟩ ⟩)
   (pentagon : ∀ {w x y z : [[C]]}
               , let x₁ : tensor ⟨tensor ⟨tensor ⟨w, x⟩ , y⟩ , z⟩ →→ tensor ⟨tensor ⟨w, tensor ⟨x, y⟩ ⟩, z⟩
                      := tensor^.hom ⟨ assoc_right ⟨w, x, y⟩, ⟨⟨z⟩⟩ ⟩ in
                 let x₂ : tensor ⟨tensor ⟨w, tensor ⟨x, y⟩ ⟩, z⟩ →→ tensor ⟨w, tensor ⟨tensor ⟨x, y⟩, z⟩ ⟩
                      := assoc_right ⟨w, tensor ⟨x, y⟩, z⟩ in
                 let x₃ : tensor ⟨w, tensor ⟨tensor ⟨x, y⟩, z⟩ ⟩ →→ tensor ⟨w, tensor ⟨x, tensor ⟨y, z⟩ ⟩ ⟩
                      := tensor^.hom ⟨ ⟨⟨w⟩⟩, assoc_right ⟨x, y, z⟩ ⟩ in
                 let y₁ : tensor ⟨tensor ⟨tensor ⟨w, x⟩ , y⟩ , z⟩ →→ tensor ⟨tensor ⟨w, x⟩, tensor ⟨y, z⟩ ⟩
                      := assoc_right ⟨tensor ⟨w, x⟩, y, z⟩ in
                 let y₂ : tensor ⟨tensor ⟨w, x⟩, tensor ⟨y, z⟩ ⟩ →→ tensor ⟨w, tensor ⟨x, tensor ⟨y, z⟩ ⟩ ⟩
                      := assoc_right ⟨w, x, tensor ⟨y, z⟩ ⟩
                 in x₃ ∘∘ x₂ ∘∘ x₁ = y₂ ∘∘ y₁)

/-! #brief A cartesian monoidal category.
-/
@[reducible] definition HasAllFiniteProducts.Monoidal {C : Cat.{(ℓobj + 1) ℓhom}}
    (C_HasAllFiniteProducts : HasAllFiniteProducts C)
    : Monoidal C
:= { tensor := HasAllFiniteProducts.PairFun C_HasAllFiniteProducts
   , unit := C_HasAllFiniteProducts^.prod []
   , assoc_left
      := { component := λ xyz, HasAllFiniteProducts.explode C_HasAllFiniteProducts [] [xyz^.fst, xyz^.snd^.fst] [xyz^.snd^.snd]
                                ∘∘ HasAllFiniteProducts.flatten C_HasAllFiniteProducts [xyz^.fst] [xyz^.snd^.fst, xyz^.snd^.snd] []
         , transport := λ xyz₁ xyz₂ f, sorry
         }
   , assoc_right
      := { component := λ xyz, HasAllFiniteProducts.explode C_HasAllFiniteProducts [xyz^.fst] [xyz^.snd^.fst, xyz^.snd^.snd] []
                                ∘∘ HasAllFiniteProducts.flatten C_HasAllFiniteProducts [] [xyz^.fst, xyz^.snd^.fst] [xyz^.snd^.snd]
         , transport := λ xyz₁ xyz₂ f, sorry
         }
   , assoc_iso :=
      { id₁ := NatTrans.eq
                (λ x, sorry)
      , id₂ := NatTrans.eq
                (λ x, sorry)
      }
   , left_unitor
      := { component := λ x, HasAllFiniteProducts.singleton_unbox C_HasAllFiniteProducts x
                              ∘∘ HasAllFiniteProducts.unit_drop C_HasAllFiniteProducts [] [x]
         , transport := begin exact sorry end
         }
   , left_unitor_inv
      := { component := λ x, HasAllFiniteProducts.unit_insert C_HasAllFiniteProducts [] [x]
                              ∘∘ HasAllFiniteProducts.singleton_box C_HasAllFiniteProducts x
         , transport := begin exact sorry end
         }
   , left_unitor_iso := begin exact sorry end
   , right_unitor
      := { component := λ x, HasAllFiniteProducts.singleton_unbox C_HasAllFiniteProducts x
                              ∘∘ HasAllFiniteProducts.unit_drop C_HasAllFiniteProducts [x] []
         , transport := begin exact sorry end
         }
   , right_unitor_inv
      := { component := λ x, HasAllFiniteProducts.unit_insert C_HasAllFiniteProducts [x] []
                              ∘∘ HasAllFiniteProducts.singleton_box C_HasAllFiniteProducts x
         , transport := begin exact sorry end
         }
   , right_unitor_iso := begin exact sorry end
   , triangle := begin exact sorry end
   , pentagon := begin exact sorry end
   }

end qp
