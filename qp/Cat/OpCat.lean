/- ----------------------------------------------------------------------------
Properties of the opposite category.
---------------------------------------------------------------------------- -/

import qp.Cat.basic

namespace Qvr
universe variables ℓobj ℓhom


/-! #brief The process of constructing the opposite category is involutive.
-/
@[simp] theorem OpCat.OpCat
    : ∀ {C : Cat.{ℓobj ℓhom}}
      , OpCat (OpCat C) = C
| (Cat.mk obj hom id circ circ_assoc circ_id_left circ_id_right)
:= rfl

end Qvr
