/- ----------------------------------------------------------------------------
Monoidal categories.
---------------------------------------------------------------------------- -/

import .basic
import .Fun

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
               , let lefty : Fun.right_comp tensor tensor ⟨x, unit, y⟩ →→ tensor ⟨x, y⟩
                      := tensor^.hom ⟨ ⟨⟨x⟩⟩, left_unitor y ⟩
                 in lefty ∘∘ assoc_right ⟨x, unit, y⟩ = tensor^.hom ⟨ right_unitor x, ⟨⟨y⟩⟩ ⟩)
   -- TODO: pentagon equality

end qp
