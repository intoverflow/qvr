/- -----------------------------------------------------------------------
Natural numbers objects.
----------------------------------------------------------------------- -/

import ..c1_basic

namespace qp

open stdaux

universe variables ℓobj ℓhom

/-! #brief A category with NNO.
-/
class HasNNO (C : Cat.{ℓobj ℓhom})
    [C_HasFinal : HasFinal C]
:= (nn : C^.obj)
   (zero : C^.hom (final C) nn)
   (succ : C^.hom nn nn)
   (univ : ∀ {A : C^.obj}
             (z : C^.hom (final C) A)
             (s : C^.hom A A)
           , C^.hom nn A)
   (comm_zero
     : ∀ {A : C^.obj}
         {z : C^.hom (final C) A}
         {s : C^.hom A A}
       , z = C^.circ (univ z s) zero)
   (comm_succ
     : ∀ {A : C^.obj}
         {z : C^.hom (final C) A}
         {s : C^.hom A A}
       , C^.circ s (univ z s) = C^.circ (univ z s) succ)
   (uniq
     : ∀ {A : C^.obj}
         {z : C^.hom (final C) A}
         {s : C^.hom A A}
         {u' : C^.hom nn A}
         (ωzero : z = C^.circ u' zero)
         (ωsucc : C^.circ s u' = C^.circ u' succ)
       , u' = univ z s)

end qp
