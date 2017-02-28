/- ----------------------------------------------------------------------------
Dependent products in LeanCat.
---------------------------------------------------------------------------- -/

import ..Cat
import .Pullback

namespace qp



/- ----------------------------------------------------------------------------
Dependent products.
---------------------------------------------------------------------------- -/

/-! #brief The dependent product functor.
-/
@[reducible] definition {ℓ} LeanCat.DepProdFun
    {T₀ T₁ : [[LeanCat.{ℓ}]]} (base : T₀ → T₁)
    : SliceCat LeanCat T₀ ⇉⇉ SliceCat LeanCat T₁
:= { obj
      := λ X
         , { dom := Σ (t₁ : T₁), ∀ (t₀ : {t₀ : T₀ // base t₀ = t₁})
                                 , { x : X^.dom // X^.hom x = t₀^.elt_of}
           , hom := λ σ, σ^.fst
           }
   , hom
      := λ X Y f
         , { hom := λ σ, { fst := σ^.fst
                         , snd := λ t₀, { elt_of := f^.hom (σ^.snd t₀)
                                        , has_property := begin
                                                            apply eq.trans (congr_fun (eq.symm f^.triangle) (σ^.snd t₀)),
                                                            apply (σ^.snd t₀)^.has_property
                                                          end
                                        }
                         }
           , triangle := rfl
           }
   , hom_id
      := λ X
         , begin
             apply SliceCat.Hom.eq,
             apply funext, intro σ,
             cases σ with t₁ σ,
             apply congr_arg (sigma.mk t₁),
             apply funext, intro t₀,
             apply subtype.eq,
             apply rfl
           end
   , hom_circ
      := λ X Y Z g f
         , begin
             apply SliceCat.Hom.eq,
             apply funext, intro σ,
             cases σ with t₁ σ,
             simp,
             apply congr_arg (sigma.mk t₁),
             apply funext, intro t₀,
             apply subtype.eq,
             apply rfl
           end
   }

/-! #brief The Lean categories have dependent products.
-/
@[reducible] definition {ℓ} LeanCat.HasAllDepProducts
    : HasAllDepProducts @LeanCat.HasAllPullbacks.{ℓ}
:= λ T₀ T₁ base
   , { dprod := LeanCat.DepProdFun base
     , adj
        := { unit := { component := λ X, { hom := λ x, { fst := X^.hom x
                                                       , snd := λ t₀, { elt_of := { elt_of := { fst := t₀^.elt_of, snd := x }
                                                                                  , has_property := t₀^.has_property
                                                                                  }
                                                                      , has_property := rfl
                                                                      }
                                                       }               
                                         , triangle := begin apply funext, intro x, apply rfl end
                                         }
                     , transport := λ X Y f, begin apply SliceCat.Hom.eq, apply funext, intro x, /- true because of f^.triangle -/ exact sorry end
                     }
           , counit := { component := λ X, { hom := λ t₀t₁σ, let t₀ := t₀t₁σ^.elt_of^.fst in
                                                             let ωt₀ := t₀t₁σ^.has_property in
                                                             let σ := t₀t₁σ^.elt_of^.snd^.snd
                                                             in (σ { elt_of := t₀, has_property := ωt₀ })^.elt_of
                                           , triangle := begin apply funext, intro t₀t₁σ,
                                                           cases t₀t₁σ with t₀t₁σ ωt₀,
                                                           cases t₀t₁σ with t₀ t₁σ,
                                                           cases t₁σ with t₁ σ,
                                                           apply eq.symm,
                                                           apply (σ {elt_of := t₀, has_property := ωt₀})^.has_property
                                                         end
                                           }
                       , transport := λ X Y f, begin apply SliceCat.Hom.eq, apply funext, intro x, dsimp, apply rfl end
                       }
           , id_left := sorry
           , id_right := sorry
           }
     }

end qp
