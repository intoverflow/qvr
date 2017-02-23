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

-- A braided monoidal category.
structure Braided {C : Cat.{ℓobj ℓhom}} (C_Monoidal : Monoidal C)
    : Type ((max ℓobj ℓhom) + 1)
:= (braid : C_Monoidal^.tensor ↣↣ Fun.flip C_Monoidal^.tensor)
   (unbraid : Fun.flip C_Monoidal^.tensor ↣↣ C_Monoidal^.tensor)
   (braid_unbraid_iso : NatIso unbraid braid)
   (hex_left
     : ∀ {x y z : [[C]]}
       , let x₁ : C_Monoidal^.tensor ⟨C_Monoidal^.tensor ⟨x, y⟩ , z⟩ →→ C_Monoidal^.tensor ⟨x, C_Monoidal^.tensor ⟨y, z⟩ ⟩
               := C_Monoidal^.assoc_right ⟨x, y, z⟩ in
         let x₂ : C_Monoidal^.tensor ⟨x, C_Monoidal^.tensor ⟨y, z⟩ ⟩ →→ C_Monoidal^.tensor ⟨C_Monoidal^.tensor ⟨y, z⟩ , x⟩
               := braid ⟨x, C_Monoidal^.tensor ⟨y, z⟩ ⟩ in
         let x₃ : C_Monoidal^.tensor ⟨C_Monoidal^.tensor ⟨y, z⟩ , x⟩ →→ C_Monoidal^.tensor ⟨y, C_Monoidal^.tensor ⟨z, x⟩ ⟩
               := C_Monoidal^.assoc_right ⟨y, z, x⟩ in
         let y₁ : C_Monoidal^.tensor ⟨C_Monoidal^.tensor ⟨x, y⟩ , z⟩ →→ C_Monoidal^.tensor ⟨C_Monoidal^.tensor ⟨y, x⟩ , z⟩
               := C_Monoidal^.tensor^.hom ⟨ braid ⟨x, y⟩, ⟨⟨z⟩⟩ ⟩ in
         let y₂ : C_Monoidal^.tensor ⟨C_Monoidal^.tensor ⟨y, x⟩ , z⟩ →→ C_Monoidal^.tensor ⟨y, C_Monoidal^.tensor ⟨x, z⟩ ⟩
               := C_Monoidal^.assoc_right ⟨y, x, z⟩ in
         let y₃ : C_Monoidal^.tensor ⟨y, C_Monoidal^.tensor ⟨x, z⟩ ⟩ →→ C_Monoidal^.tensor ⟨y, C_Monoidal^.tensor ⟨z, x⟩ ⟩
               := C_Monoidal^.tensor^.hom ⟨ ⟨⟨y⟩⟩, braid ⟨x, z⟩ ⟩
         in y₃ ∘∘ y₂ ∘∘ y₁ = x₃ ∘∘ x₂ ∘∘ x₁)
    (hex_right
      : ∀ {x y z : [[C]]}
        , let x₁ : C_Monoidal^.tensor ⟨x, C_Monoidal^.tensor ⟨y, z⟩ ⟩ →→ C_Monoidal^.tensor ⟨C_Monoidal^.tensor ⟨x, y⟩ , z⟩
                := C_Monoidal^.assoc_left ⟨x, y, z⟩ in
          let x₂ : C_Monoidal^.tensor ⟨C_Monoidal^.tensor ⟨x, y⟩ , z⟩ →→ C_Monoidal^.tensor ⟨z, C_Monoidal^.tensor ⟨x, y⟩ ⟩
                := braid ⟨C_Monoidal^.tensor ⟨x, y⟩, z⟩ in
          let x₃ : C_Monoidal^.tensor ⟨z, C_Monoidal^.tensor ⟨x, y⟩ ⟩ →→ C_Monoidal^.tensor ⟨C_Monoidal^.tensor ⟨z, x⟩ , y⟩
                := C_Monoidal^.assoc_left ⟨z, x, y⟩ in
          let y₁ : C_Monoidal^.tensor ⟨x, C_Monoidal^.tensor ⟨y, z⟩ ⟩ →→ C_Monoidal^.tensor ⟨x, C_Monoidal^.tensor ⟨z, y⟩ ⟩
                := C_Monoidal^.tensor^.hom ⟨ ⟨⟨x⟩⟩, braid ⟨y, z⟩ ⟩ in
          let y₂ : C_Monoidal^.tensor ⟨x, C_Monoidal^.tensor ⟨z, y⟩ ⟩ →→ C_Monoidal^.tensor ⟨C_Monoidal^.tensor ⟨x, z⟩ , y⟩
                := C_Monoidal^.assoc_left ⟨x, z, y⟩ in
          let y₃ : C_Monoidal^.tensor ⟨C_Monoidal^.tensor ⟨x, z⟩ , y⟩ →→ C_Monoidal^.tensor ⟨C_Monoidal^.tensor ⟨z, x⟩ , y⟩
                := C_Monoidal^.tensor^.hom ⟨ braid ⟨x, z⟩, ⟨⟨y⟩⟩ ⟩
          in y₃ ∘∘ y₂ ∘∘ y₁ = x₃ ∘∘ x₂ ∘∘ x₁)

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
