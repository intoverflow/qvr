/- ----------------------------------------------------------------------------
Properties of FinLeanCat.
---------------------------------------------------------------------------- -/

import .basic
import .Cone
import .SubObjClass
import ..util

namespace qp
universe variables ℓ



/- ----------------------------------------------------------------------------
Initial and final objects.
---------------------------------------------------------------------------- -/

/-! #brief poly_empty is an initial object in FinLeanCat.
-/
@[reducible] definition FinLeanCat.init
    : IsInit FinLeanCat.{ℓ}
             { T := poly_empty.{ℓ}
             , is_finite := poly_empty.FinType
             }
:= { init := λ A, poly_empty.elim
   , uniq := λ A f, begin
                      apply funext, intro e,
                      exact poly_empty.elim e
                    end
   }

/-! #brief poly_unit is a final object in FinLeanCat.
-/
@[reducible] definition FinLeanCat.final
    : IsFinal FinLeanCat.{ℓ}
              { T := poly_unit.{ℓ}
              , is_finite := poly_unit.FinType
              }
:= { final := λ A a, poly_unit.star
   , uniq := λ A f, begin
                      apply funext, intro a,
                      apply poly_unit.uniq
                    end
   }



/- ----------------------------------------------------------------------------
Subobject classifier.
---------------------------------------------------------------------------- -/

/-! #brief Comparator used to define the characteristic function for FinLeanCat.SubObjClass.
-/
@[reducible] definition FinLeanCat.SubObjClass.compare_via {A B : BxFinType.{ℓ}}
    (f : A^.T → B^.T)
    (b : B^.T)
    (a : A^.T)
    : bool
:= if B^.is_finite^.n_of b = B^.is_finite^.n_of (f a)
    then bool.tt
    else bool.ff

/-! #brief Comparator used to define the characteristic function for FinLeanCat.SubObjClass.
-/
@[reducible] definition FinLeanCat.SubObjClass.in_image {A B : BxFinType.{max 1 ℓ}}
    (f : A^.T → B^.T)
    (b : B^.T)
    : poly_bool.{ℓ}
:= if list.any (fin.enum A^.is_finite^.of_n)
               (FinLeanCat.SubObjClass.compare_via f b)
    then poly_bool.tt
    else poly_bool.ff

/-! #brief The image is in the image.
-/
@[simp] theorem FinLeanCat.SubObjClass.image_in_image {A B : BxFinType.{max 1 ℓ}}
    {f : A^.T → B^.T}
    {a : A^.T}
    : FinLeanCat.SubObjClass.in_image f (f a) = poly_bool.tt
:= sorry

/-! #brief FinLeanCat has a subobject classifier.
-/
@[reducible] definition FinLeanCat.SubObjClass
    : SubObjClass FinLeanCat.{max 1 ℓ} FinLeanCat.final
:= { Ω := { T := poly_bool.{ℓ}
          , is_finite := poly_bool.FinType
          }
   , true := λ s, poly_bool.tt
   , true_monic
      := λ A g₁ g₂ ω
         , begin
             apply funext, intro a,
             apply eq.trans poly_unit.uniq (eq.symm poly_unit.uniq)
           end
   , char
      := λ U X f f_monic x, FinLeanCat.SubObjClass.in_image f x
   , char_pullback
      := λ U X f f_monic
         , IsPullback.show _ _ _ _
           (λ cone cn,
             begin
               assert magic : X^.T → U^.T, { exact sorry },
               apply magic,
               apply cone^.is_cone^.proj CoSpanCat.Obj.a cn,
             end)
           begin apply funext, intro u, apply FinLeanCat.SubObjClass.image_in_image end
           begin intro cone, apply funext, intro cn, simp, exact sorry end
           begin intro cone, apply funext, intro cn, apply poly_unit.uniq end
           begin intros cone h, exact sorry end
   , char_uniq
      := λ U X f f_monic char' ωpb
         , begin
             apply funext,
             intro x,
             exact sorry
           end
   }

end qp
