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

/-! #brief pempty is an initial object in FinLeanCat.
-/
@[reducible] definition FinLeanCat.Init
    : Init FinLeanCat.{ℓ}
:= { obj := { T := pempty.{ℓ + 1}
            , is_finite := pempty.FinType
            }
   , hom := λ A, pempty.elim
   , uniq := λ A f, begin
                      apply pfunext, intro e,
                      exact pempty.elim e
                    end
   }

/-! #brief punit is a final object in FinLeanCat.
-/
@[reducible] definition FinLeanCat.Final
    : Final FinLeanCat.{ℓ}
:= { obj := { T := punit.{ℓ + 1}
            , is_finite := punit.FinType
            }
   , hom := λ A a, punit.star
   , uniq := λ A f, begin
                      apply pfunext, intro a,
                      apply punit.uniq
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
@[reducible] definition FinLeanCat.SubObjClass.in_image {A B : BxFinType.{ℓ}}
    (f : A^.T → B^.T)
    (b : B^.T)
    : pbool.{ℓ}
:= if list.any (fin.enum A^.is_finite^.of_n)
       (FinLeanCat.SubObjClass.compare_via f b)
        = bool.tt
    then pbool.tt
    else pbool.ff

/-! #brief The image is in the image.
-/
@[simp] theorem FinLeanCat.SubObjClass.image_in_image {A B : BxFinType.{ℓ}}
    {f : A^.T → B^.T}
    {a : A^.T}
    : FinLeanCat.SubObjClass.in_image f (f a) = pbool.tt
:= sorry

/-! #brief The right-inverse of a monic.
-/
@[reducible] definition FinLeanCat.monic_inv {A B : BxFinType.{ℓ}}
    (f : A^.T → B^.T)
    (f_monic : @IsMonic FinLeanCat.{ℓ} A B f)
    (b : B^.T)
    (ωb : FinLeanCat.SubObjClass.in_image f b = pbool.tt)
    : A^.T
:= sorry

/-! #brief FinLeanCat.monic_inv f is a right inverse of f.
-/
@[simp] theorem FinLeanCat.monic_inv.right_inv {A B : BxFinType.{ℓ}}
    (f : A^.T → B^.T)
    {f_monic : @IsMonic FinLeanCat.{ℓ} A B f}
    {b : B^.T}
    {ωb : FinLeanCat.SubObjClass.in_image f b = pbool.tt}
    : f (FinLeanCat.monic_inv f f_monic b ωb) = b
:= sorry

/-
/-! #brief FinLeanCat has a subobject classifier.
-/
@[reducible] definition FinLeanCat.SubObjClass
    : SubObjClass FinLeanCat.{ℓ} FinLeanCat.final
:= { Ω := { T := pbool.{ℓ}
          , is_finite := pbool.FinType
          }
   , true := λ s, pbool.tt
   , true_monic
      := λ A g₁ g₂ ω
         , begin
             apply funext, intro a,
             apply eq.trans punit.uniq (eq.symm punit.uniq)
           end
   , char
      := λ U X f f_monic x, FinLeanCat.SubObjClass.in_image f x
   , char_pullback
      := λ U X f f_monic
         , IsPullback.show _ _ _ _
           (λ cone cn,
             FinLeanCat.monic_inv f f_monic (cone^.is_cone^.proj CoSpanCat.Obj.a cn)
               begin
                 --apply eq.trans (eq.symm (congr_fun (cone^.is_cone^.triangle CoSpanCat.Hom.a) cn)),
                 --apply eq.trans (congr_fun (cone^.is_cone^.triangle CoSpanCat.Hom.b) cn),
                 --apply rfl
                 exact sorry
               end)
           begin apply funext, intro u, apply FinLeanCat.SubObjClass.image_in_image end
           begin intro cone, apply funext, intro cn, apply eq.symm, simp, apply FinLeanCat.monic_inv.right_inv f end
           begin intro cone, apply funext, intro cn, apply punit.uniq end
           begin intros cone h, apply funext, intro cn, apply eq.symm, exact sorry end
   , char_uniq
      := λ U X f f_monic char' ωpb
         , begin
             apply funext,
             intro x,
             exact sorry
           end
   }
-/

end qp
