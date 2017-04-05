/- -----------------------------------------------------------------------
Exponential obejcts.
----------------------------------------------------------------------- -/

import ..c1_basic
import ..c2_limits

namespace qp

open stdaux

universe variables ℓobj ℓhom

class HasExp {C : Cat.{ℓobj ℓhom}}
    (X Y : C^.obj)
:= (exp : C^.obj)
   (ev
     : ∀ [exp_Y_HasFinProduct : HasFinProduct C [exp, Y]]
       , C^.hom (finproduct C [exp, Y]) X)
   (univ
     : ∀ (Z : C^.obj) [Z_Y_HasFinProduct : HasFinProduct C [Z, Y]]
         (e : C^.hom (finproduct C [Z, Y]) X)
       , C^.hom Z exp)
   (factor
     : ∀ [exp_Y_HasFinProduct : HasFinProduct C [exp, Y]]
         (Z : C^.obj) [Z_Y_HasFinProduct : HasFinProduct C [Z, Y]]
         (e : C^.hom (finproduct C [Z, Y]) X)
       , e = ev ∘∘ finproduct.hom (univ Z e ↗ C^.id Y ↗↗))
   (uniq
     : ∀ [exp_Y_HasFinProduct : HasFinProduct C [exp, Y]]
         (ev' : C^.hom (finproduct C [exp, Y]) X)
         (ωev' : ∀ (Z : C^.obj) [Z_Y_HasFinProduct : HasFinProduct C [Z, Y]]
                   (e : C^.hom (finproduct C [Z, Y]) X)
                 , e = ev' ∘∘ finproduct.hom (univ Z e ↗ C^.id Y ↗↗))
       , ev' = ev)

end qp
