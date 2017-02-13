/- ----------------------------------------------------------------------------
Finite categories.
---------------------------------------------------------------------------- -/

import .basic
import ..util

namespace qp
universe variables ℓobj ℓhom



-- A finite category.
structure Cat.Fin (C : Cat.{ℓobj ℓhom}) : Type (max 1 ℓobj ℓhom)
:= (obj : FinType [[C]])
   (hom : ∀ (x y : [[C]]), FinType (x →→ y))

-- TODO: Fix docstring!
--/-! #brief EmptyCat is finite.
---/
@[reducible] definition EmptyCat.Fin : Cat.Fin EmptyCat.{ℓobj ℓhom}
:= { obj := poly_empty.FinType
   , hom := λ x y, poly_empty.FinType
   }

/-! #brief StarCat is finite.
-/
@[reducible] definition StarCat.Fin : Cat.Fin StarCat.{ℓobj ℓhom}
:= { obj := poly_unit.FinType
   , hom := λ x y, poly_unit.FinType
   }

end qp
