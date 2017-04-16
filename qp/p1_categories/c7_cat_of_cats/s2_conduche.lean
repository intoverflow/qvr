/- -----------------------------------------------------------------------
Fibrations.
----------------------------------------------------------------------- -/

import ..c1_basic

namespace qp

open stdaux

universe variables ℓobjb ℓhomb ℓobj ℓhom



/- -----------------------------------------------------------------------
Conduché functors.
----------------------------------------------------------------------- -/

/-! #brief A Conduché factorization.
-/
structure ConducheFact {E : Cat.{ℓobj ℓhom}} {B : Cat.{ℓobjb ℓhomb}}
    (P : Fun E B)
    {a c : E^.obj} (f : E^.hom a c)
    {b : B^.obj}
    (h : B^.hom b (P^.obj c))
    (g : B^.hom (P^.obj a) b)
    (ω : P^.hom f = h ∘∘ g)
:= (obj : E^.obj)
   (obj_im : P^.obj obj = b)
   (left : E^.hom obj c)
   (left_im : P^.hom left = h ∘∘ cast_hom obj_im)
   (right : E^.hom a obj)
   (right_im : P^.hom right = cast_hom (eq.symm obj_im) ∘∘ g)
   (comm : f = left ∘∘ right)

/-! #brief A Conduché functor.
-/
structure Conduche {E : Cat.{ℓobj ℓhom}} {B : Cat.{ℓobjb ℓhomb}}
    (P : Fun E B)
:= (factorize
     : ∀ {a c : E^.obj} (f : E^.hom a c)
         {b : B^.obj}
         (h : B^.hom b (P^.obj c))
         (g : B^.hom (P^.obj a) b)
         (ω : P^.hom f = h ∘∘ g)
       , ConducheFact P f h g ω)
   (zigzag
     : ∀ {a c : E^.obj} {f : E^.hom a c}
         {b : B^.obj}
         {h : B^.hom b (P^.obj c)}
         {g : B^.hom (P^.obj a) b}
         {ω : P^.hom f = h ∘∘ g}
         (fac₁ fac₂ : ConducheFact P f h g ω)
       , E^.hom fac₁^.obj fac₂^.obj)
   (zigzag_im
     : ∀ {a c : E^.obj} {f : E^.hom a c}
         {b : B^.obj}
         {h : B^.hom b (P^.obj c)}
         {g : B^.hom (P^.obj a) b}
         {ω : P^.hom f = h ∘∘ g}
         (fac₁ fac₂ : ConducheFact P f h g ω)
       , P^.hom (zigzag fac₁ fac₂) = cast_hom (eq.trans fac₁^.obj_im (eq.symm fac₂^.obj_im)))
   (zigzag_left
     : ∀ {a c : E^.obj} {f : E^.hom a c}
         {b : B^.obj}
         {h : B^.hom b (P^.obj c)}
         {g : B^.hom (P^.obj a) b}
         {ω : P^.hom f = h ∘∘ g}
         (fac₁ fac₂ : ConducheFact P f h g ω)
       , fac₁^.left = fac₂^.left ∘∘ zigzag fac₁ fac₂)
   (zigzag_right
     : ∀ {a c : E^.obj} {f : E^.hom a c}
         {b : B^.obj}
         {h : B^.hom b (P^.obj c)}
         {g : B^.hom (P^.obj a) b}
         {ω : P^.hom f = h ∘∘ g}
         (fac₁ fac₂ : ConducheFact P f h g ω)
       , fac₂^.right = zigzag fac₁ fac₂ ∘∘ fac₁^.right)



end qp
