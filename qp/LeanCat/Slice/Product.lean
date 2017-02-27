/- ----------------------------------------------------------------------------
Products in slices of LeanCat.
---------------------------------------------------------------------------- -/

import ...Cat
import ..Pullback

namespace qp



/- ----------------------------------------------------------------------------
Products in the slice categories.
---------------------------------------------------------------------------- -/

/-! #brief Slices of Lean categories have all finite products.
-/
@[reducible] definition {ℓ} LeanCat.Slice.HasAllFiniteProducts
    (T : [[LeanCat.{ℓ}]])
    : HasAllFiniteProducts (SliceCat LeanCat.{ℓ} T) SliceCat.Final
:= { prod := λ c₁ c₂
             , Product.show (bool.pick c₁ c₂)
                { dom := LeanCat.HasAllPullbacks c₁^.hom c₂^.hom
                , hom := c₁^.hom ∘∘ Pullback.π₁ (LeanCat.HasAllPullbacks c₁^.hom c₂^.hom)
                }
                (λ b, bool.cases_on b
                       { hom := Pullback.π₂ (LeanCat.HasAllPullbacks c₁^.hom c₂^.hom)
                       , triangle := begin apply funext, intro ab, dsimp, exact sorry end
                       }
                       { hom := Pullback.π₁ (LeanCat.HasAllPullbacks c₁^.hom c₂^.hom)
                       , triangle := begin apply funext, intro ab, dsimp, exact sorry end
                       })
                (λ cone, { hom := λ cn, { elt_of := { fst := (cone^.proj bool.tt)^.hom cn
                                                    , snd := (cone^.proj bool.ff)^.hom cn
                                                    }
                                        , has_property := sorry
                                        }
                         , triangle := sorry
                         })
                sorry
                sorry
   , prod_id_left₁ := λ U, { hom := λ ab, ab^.elt_of^.snd
                           , triangle := begin apply funext, intro ab, exact sorry end
                           }
   , prod_id_left₂ := λ U, { hom := λ u, { elt_of := { fst := U^.hom u, snd := u }
                                         , has_property := rfl
                                         }
                           , triangle := begin apply funext, intro u, apply rfl end
                           }
   , prod_id_left := λ U, { id₁ := begin apply SliceCat.Hom.eq, apply funext, intro ab, exact sorry end
                          , id₂ := begin apply SliceCat.Hom.eq, apply funext, intro u, apply rfl end
                          }
   , prod_id_right₁ := λ U, { hom := λ ab, ab^.elt_of^.fst
                            , triangle := begin apply funext, intro ab, exact sorry end
                            }
   , prod_id_right₂ := λ U, { hom := λ u, { elt_of := { fst := u, snd := U^.hom u }
                                          , has_property := rfl
                                          }
                            , triangle := begin apply funext, intro u, apply rfl end
                            }
   , prod_id_right := λ U, { id₁ := begin apply SliceCat.Hom.eq, apply funext, intro ab, exact sorry end
                           , id₂ := begin apply SliceCat.Hom.eq, apply funext, intro u, apply rfl end
                           }
   }

/-! #brief Slices of Lean categories are cartesian monoidal.
-/
@[reducible] definition {ℓ} LeanCat.Slice.CartesianMonoidal
    (T : [[LeanCat.{ℓ}]])
    : IsMonoidal (SliceCat LeanCat.{ℓ} T)
                 (PairFun (LeanCat.Slice.HasAllFiniteProducts T))
                 SliceCat.Final^.obj
:= HasAllFiniteProducts.Monoidal (LeanCat.Slice.HasAllFiniteProducts T)

/-! #brief Slices of Lean categories are cartesian monoidal.
-/
@[reducible] definition {ℓ} LeanCat.Slice.CartesianSymmetric
    (T : [[LeanCat.{ℓ}]])
    : IsSymmetric (SliceCat LeanCat.{ℓ} T)
                  (LeanCat.Slice.CartesianMonoidal T)
                  (PairFun.BraidTrans (LeanCat.Slice.HasAllFiniteProducts T))
:= HasAllFiniteProducts.Symmetric (LeanCat.Slice.HasAllFiniteProducts T)

/-! #brief Internal hom in a slice of a Lean category.
-/
@[reducible] definition {ℓ} LeanCat.Slice.InternalHom
    (T : [[LeanCat.{ℓ}]])
    : [[SliceCat LeanCat.{ℓ} T]] → SliceCat LeanCat.{ℓ} T ⇉⇉ SliceCat LeanCat.{ℓ} T
:= λ y, sorry

end qp
