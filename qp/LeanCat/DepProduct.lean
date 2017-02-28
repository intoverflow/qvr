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
           , hom := sigma.fst
           }
   , hom
      := λ X Y f
         , { hom := λ σ, { fst := σ^.fst
                         , snd := λ t₀, { elt_of := f^.hom (σ^.snd t₀)^.elt_of
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

/-! #brief Component of unit adjoint of dependent product and base change.
-/
@[reducible] definition {ℓ} LeanCat.BaseChangeDepProd_Unit.component
    {T₀ T₁ : [[LeanCat.{ℓ}]]} (base : T₀ → T₁)
    (X : [[SliceCat LeanCat T₁]])
    : (SliceCat LeanCat T₁)^.hom
        X
        ((LeanCat.DepProdFun base □□ BaseChangeFun (@HasAllPullbacks.HasAllPullbacksAlong _ @LeanCat.HasAllPullbacks _ _ base)) X)
:= { hom
      := λ x
         , { fst := X^.hom x
           , snd
              := λ t₀
                 , { elt_of
                      := { elt_of := { fst := t₀^.elt_of
                                     , snd := x
                                     }
                         , has_property := t₀^.has_property
                         }
                   , has_property := rfl
                   }
                 }
   , triangle
      := begin
           apply funext,
           intro x,
           apply rfl
         end
   }

/-! #brief Transport of unit adjoint of dependent product and base change.
-/
@[reducible] definition {ℓ} LeanCat.BaseChangeDepProd_Unit.transport
    {T₀ T₁ : [[LeanCat.{ℓ}]]} (base : T₀ → T₁)
    : ∀ {X Y : [[SliceCat LeanCat T₁]]} {f : (SliceCat LeanCat T₁)^.hom X Y}
      , (SliceCat LeanCat T₁)^.circ (LeanCat.BaseChangeDepProd_Unit.component base Y) f
         = (SliceCat LeanCat T₁)^.circ
             ((LeanCat.DepProdFun base □□ BaseChangeFun (@HasAllPullbacks.HasAllPullbacksAlong _ @LeanCat.HasAllPullbacks _ _ base))^.hom f)
             (LeanCat.BaseChangeDepProd_Unit.component base X)
| (SliceCat.Obj.mk X Xhom) (SliceCat.Obj.mk Y Yhom) (SliceCat.Hom.mk f ωXhom)
:= sorry
/- begin
     dsimp at ωXhom,
     apply SliceCat.Hom.eq,
     apply funext,
     intro x,
     dsimp,
     refine sigma.eq _ _,
     { dsimp, rw ωXhom },
     { apply funext,
       intro t₀,
       cases t₀ with t₀ ωt₀,
       apply subtype.eq,
       apply subtype.eq,
       apply prod.eq,
       { exact sorry -- equals t₀
       },
       { exact sorry -- equals f x
       }
     }
   end -/

/-! #brief Unit adjoint of dependent product and base change.
-/
@[reducible] definition {ℓ} LeanCat.BaseChangeDepProd_Unit
    {T₀ T₁ : [[LeanCat.{ℓ}]]} (base : T₀ → T₁)
    : Fun.id (SliceCat LeanCat T₁)
       ↣↣ LeanCat.DepProdFun base
           □□ BaseChangeFun (@HasAllPullbacks.HasAllPullbacksAlong _ @LeanCat.HasAllPullbacks _ _ base)
:= { component := LeanCat.BaseChangeDepProd_Unit.component base
   , transport := λ X Y f, LeanCat.BaseChangeDepProd_Unit.transport base
/-
      := begin --λ X Y f
         --, begin
             cases X with X Xhom,
             cases Y with Y Yhom,
             cases f with f f_triangle,
             dsimp at f,
             dsimp at f_triangle,
             apply SliceCat.Hom.eq,
             apply funext,
             intro x,
             /-
             subst f_triangle,
             apply congr_arg (sigma.mk (Yhom (f x))),
             apply funext,
             intro t₀,
             cases t₀ with t₀ ωt₀,
             apply rfl
             -/
             refine sigma.eq _ _,
             { subst f_triangle },
             { subst f_triangle,
               apply funext,
               intro t₀,
               cases t₀ with t₀ ωt₀,
               apply rfl
             }
           end
-/
   }

/-! #brief Co-unit adjoint of dependent product and base change.
-/
@[reducible] definition {ℓ} LeanCat.BaseChangeDepProd_CoUnit
    {T₀ T₁ : [[LeanCat.{ℓ}]]} (base : T₀ → T₁)
    : BaseChangeFun (@HasAllPullbacks.HasAllPullbacksAlong _ @LeanCat.HasAllPullbacks _ _ base)
       □□ LeanCat.DepProdFun base
      ↣↣ Fun.id (SliceCat LeanCat T₀)
:= { component
      := λ X, { hom := λ t₀t₁σ, let t₀ := t₀t₁σ^.elt_of^.fst in
                                let ωt₀ := t₀t₁σ^.has_property in
                                let σ := t₀t₁σ^.elt_of^.snd^.snd
                                in (σ { elt_of := t₀, has_property := ωt₀ })^.elt_of
              , triangle
                 := begin
                      apply funext, intro t₀t₁σ,
                      cases t₀t₁σ with t₀t₁σ ωt₀,
                      cases t₀t₁σ with t₀ t₁σ,
                      cases t₁σ with t₁ σ,
                      apply eq.symm,
                      apply (σ {elt_of := t₀, has_property := ωt₀})^.has_property
                    end
              }
   , transport
      := λ X Y f
         , begin
             apply SliceCat.Hom.eq,
             apply funext,
             intro x,
             dsimp,
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
        := { unit := LeanCat.BaseChangeDepProd_Unit base
           , counit := LeanCat.BaseChangeDepProd_CoUnit base
           , id_left
              := λ X
                 , begin
                     apply SliceCat.Hom.eq,
                     apply funext,
                     intro t₀x,
                     cases t₀x with t₀x ωt₀,
                     cases t₀x with t₀ x,
                     apply subtype.eq,
                     apply rfl
                   end
           , id_right
              := λ X
                 , begin
                     apply SliceCat.Hom.eq,
                     apply funext,
                     intro t₁σ,
                     cases t₁σ with t₁ σ,
                     apply congr_arg (sigma.mk t₁),
                     apply funext,
                     intro t₀,
                     cases t₀ with t₀ ωt₀,
                     apply subtype.eq,
                     exact rfl
                   end
           }
     }

end qp
