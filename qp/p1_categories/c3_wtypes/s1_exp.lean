/- -----------------------------------------------------------------------
Exponential obejcts.
----------------------------------------------------------------------- -/

import ..c1_basic
import ..c2_limits

namespace qp

open stdaux

universe variables ℓobj ℓhom

class HasExp {C : Cat.{ℓobj ℓhom}}
    (x : C^.obj) (y : list C^.obj)
:= (exp : ∀ [C_HasAllFinProducts : HasAllFinProducts C]
          , C^.obj)
   (ev
     : ∀ [C_HasAllFinProducts : HasAllFinProducts C]
       , C^.hom (finproduct C (exp :: y)) x)
   (univ
     : ∀ [C_HasAllFinProducts : HasAllFinProducts C]
         (z : C^.obj)
         (e : C^.hom (finproduct C (z :: y)) x)
       , C^.hom z exp)
   (factor
     : ∀ [C_HasAllFinProducts : HasAllFinProducts C]
         (z : C^.obj)
         (e : C^.hom (finproduct C (z :: y)) x)
       , e = ev
              ∘∘ finproduct.flatten_right [exp] y
              ∘∘ finproduct.hom (univ z e ↗ C^.id (finproduct C y) ↗↗)
              ∘∘ finproduct.unflatten_right [z] y)
   (uniq
     : ∀ [C_HasAllFinProducts : HasAllFinProducts C]
         (ev' : C^.hom (finproduct C (exp :: y)) x)
         (ωev' : ∀ (z : C^.obj)
                   (e : C^.hom (finproduct C (z :: y)) x)
                 , e = ev'
                        ∘∘ finproduct.flatten_right [exp] y
                        ∘∘ finproduct.hom (univ z e ↗ C^.id (finproduct C y) ↗↗)
                        ∘∘ finproduct.unflatten_right [z] y)
       , ev' = ev)

instance HasExp.HasExp₀ {C : Cat.{ℓobj ℓhom}}
    (X : C^.obj)
    : HasExp X []
:= { exp := λ C_HasAllFinProducts, X
   , ev := λ C_HasAllFinProducts
           , @finproduct.π C [X]
                (@HasAllFinProducts.HasFinProduct _ C_HasAllFinProducts [X])
                (fin_of 0)
   , univ
      := λ C_HasAllFinProducts A f
         , f ∘∘ @finproduct.singleton.to C A (@HasAllFinProducts.HasFinProduct _ C_HasAllFinProducts [A])
   , factor := λ C_HasAllFinProducts A e
               , sorry
   , uniq := λ C_HasAllFinProducts ev' ωev'
             , sorry
   }

end qp
