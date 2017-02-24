/- ----------------------------------------------------------------------------
Monoidal categories.
---------------------------------------------------------------------------- -/

import .basic
import .Fun

namespace qp
universe variables ℓobj ℓhom



-- A monoidal category.
structure IsMonoidal (C : Cat.{ℓobj ℓhom})
    (tensor : C ×× C ⇉⇉ C)
    (unit : [[C]])
    : Type ((max ℓobj ℓhom) + 1)
:= (assoc_left : Fun.right_comp tensor tensor ↣↣ Fun.left_comp tensor tensor □□ ProdCat.assoc_left)
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

/-! #brief The left hexagon diagram.
-/
@[reducible] definition IsBraided.hex_right_diagram {C : Cat.{ℓobj ℓhom}}
    {tensor : C ×× C ⇉⇉ C}
    {unit : [[C]]}
    (C_Monoidal : IsMonoidal C tensor unit)
    (braid : tensor ↣↣ tensor □□ ProdCat.flip)
    : Prop
:= ∀ {x y z : [[C]]}
   , let x₁ : tensor ⟨tensor ⟨x, y⟩ , z⟩ →→ tensor ⟨x, tensor ⟨y, z⟩ ⟩
           := C_Monoidal^.assoc_right ⟨x, y, z⟩ in
     let x₂ : tensor ⟨x, tensor ⟨y, z⟩ ⟩ →→ tensor ⟨tensor ⟨y, z⟩ , x⟩
           := braid ⟨x, tensor ⟨y, z⟩ ⟩ in
     let x₃ : tensor ⟨tensor ⟨y, z⟩ , x⟩ →→ tensor ⟨y, tensor ⟨z, x⟩ ⟩
           := C_Monoidal^.assoc_right ⟨y, z, x⟩ in
     let y₁ : tensor ⟨tensor ⟨x, y⟩ , z⟩ →→ tensor ⟨tensor ⟨y, x⟩ , z⟩
           := tensor^.hom ⟨ braid ⟨x, y⟩, ⟨⟨z⟩⟩ ⟩ in
     let y₂ : tensor ⟨tensor ⟨y, x⟩ , z⟩ →→ tensor ⟨y, tensor ⟨x, z⟩ ⟩
           := C_Monoidal^.assoc_right ⟨y, x, z⟩ in
     let y₃ : tensor ⟨y, tensor ⟨x, z⟩ ⟩ →→ tensor ⟨y, tensor ⟨z, x⟩ ⟩
           := tensor^.hom ⟨ ⟨⟨y⟩⟩, braid ⟨x, z⟩ ⟩
     in y₃ ∘∘ y₂ ∘∘ y₁ = x₃ ∘∘ x₂ ∘∘ x₁

/-! #brief The right hexagon diagram.
-/
@[reducible] definition IsBraided.hex_left_diagram {C : Cat.{ℓobj ℓhom}}
    {tensor : C ×× C ⇉⇉ C}
    {unit : [[C]]}
    (C_Monoidal : IsMonoidal C tensor unit)
    (braid : tensor ↣↣ tensor □□ ProdCat.flip)
    : Prop
:= ∀ {x y z : [[C]]}
   , let x₁ : tensor ⟨x, tensor ⟨y, z⟩ ⟩ →→ tensor ⟨tensor ⟨x, y⟩ , z⟩
           := C_Monoidal^.assoc_left ⟨x, y, z⟩ in
     let x₂ : tensor ⟨tensor ⟨x, y⟩ , z⟩ →→ tensor ⟨z, tensor ⟨x, y⟩ ⟩
           := braid ⟨tensor ⟨x, y⟩, z⟩ in
     let x₃ : tensor ⟨z, tensor ⟨x, y⟩ ⟩ →→ tensor ⟨tensor ⟨z, x⟩ , y⟩
           := C_Monoidal^.assoc_left ⟨z, x, y⟩ in
     let y₁ : tensor ⟨x, tensor ⟨y, z⟩ ⟩ →→ tensor ⟨x, tensor ⟨z, y⟩ ⟩
           := tensor^.hom ⟨ ⟨⟨x⟩⟩, braid ⟨y, z⟩ ⟩ in
     let y₂ : tensor ⟨x, tensor ⟨z, y⟩ ⟩ →→ tensor ⟨tensor ⟨x, z⟩ , y⟩
           := C_Monoidal^.assoc_left ⟨x, z, y⟩ in
     let y₃ : tensor ⟨tensor ⟨x, z⟩ , y⟩ →→ tensor ⟨tensor ⟨z, x⟩ , y⟩
           := tensor^.hom ⟨ braid ⟨x, z⟩, ⟨⟨y⟩⟩ ⟩
     in y₃ ∘∘ y₂ ∘∘ y₁ = x₃ ∘∘ x₂ ∘∘ x₁

-- A braided monoidal category.
structure IsBraided {C : Cat.{ℓobj ℓhom}}
    {tensor : C ×× C ⇉⇉ C}
    {unit : [[C]]}
    (C_Monoidal : IsMonoidal C tensor unit)
    (braid : tensor ↣↣ tensor □□ ProdCat.flip)
    (unbraid : tensor □□ ProdCat.flip ↣↣ tensor)
    : Type ((max ℓobj ℓhom) + 1)
:= (unbraid_braid_iso : NatIso unbraid braid)
   (hex_right : IsBraided.hex_right_diagram C_Monoidal braid)
   (hex_left : IsBraided.hex_left_diagram C_Monoidal braid)

/-! #brief A symmetric monoidal category.
-/
@[reducible] definition IsSymmetric (C : Cat.{ℓobj ℓhom})
    {tensor : C ×× C ⇉⇉ C}
    {unit : [[C]]}
    (C_Monoidal : IsMonoidal C tensor unit)
    (braid : tensor ↣↣ tensor □□ ProdCat.flip)
    : Type ((max ℓobj ℓhom) + 1)
:= IsBraided C_Monoidal braid (NatTrans.flip braid)

/-! #brief Helper for showing a symmetric monoidal category.
-/
@[reducible] definition IsSymmetric.show {C : Cat.{ℓobj ℓhom}}
    {tensor : C ×× C ⇉⇉ C}
    {unit : [[C]]}
    (C_Monoidal : IsMonoidal C tensor unit)
    (braid : tensor ↣↣ tensor □□ ProdCat.flip)
    (ωiso : NatIso (NatTrans.flip braid) braid)
    (ωright : IsBraided.hex_right_diagram C_Monoidal braid)
    : IsSymmetric C C_Monoidal braid
:= { unbraid_braid_iso := ωiso
   , hex_right := @ωright
   , hex_left := λ x y z , sorry -- should follow from ωiso and ωright
   }

end qp
