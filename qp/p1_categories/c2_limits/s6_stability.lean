/- -----------------------------------------------------------------------
Stability of limits and colimits.
----------------------------------------------------------------------- -/

import .s1_limits
import .s2_products
import .s3_pullbacks

namespace qp

open stdaux

universe variables ℓ ℓobj ℓhom



/- -----------------------------------------------------------------------
Stability of pullbacks and coproducts.
----------------------------------------------------------------------- -/

/-! #brief The hom Σ (A × B) → A × Σ B.
-/
definition coproduct_pullback.pullback_coproduct {C : Cat.{ℓobj ℓhom}}
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasAllCoProducts : HasAllCoProducts C]
    {x y : C^.obj} (f : C^.hom x y)
    {I : Type ℓ}
    (factors : I → C^.obj)
    (h : ∀ (i : I), C^.hom (factors i) y)
    : C^.hom (coproduct C (λ (i : I), pullback C (f ↗→ h i ↗→↗)))
             (pullback C (f ↗→ coproduct.univ C factors (CoProductCone.mk y h) ↗→↗))
:= let ccone₁ : CoProductCone C (λ (i : I), pullback C (f↗→(h i)↗→↗))
             := CoProductCone.mk x (λ i, pullback.π C (f↗→(h i)↗→↗) (@fin_of 1 0))
in let h₁ : ⟦C : coproduct C (λ (i : I), pullback C (f↗→(h i)↗→↗)) →→ x⟧
         := coproduct.univ C (λ (i : I), pullback C (f↗→(h i)↗→↗)) ccone₁
in let ccone₂ : CoProductCone C (λ (i : I), pullback C (f↗→(h i)↗→↗))
             := CoProductCone.mk (coproduct C factors) (λ i, coproduct.ι C factors i ∘∘ pullback.π C (f↗→(h i)↗→↗) (@fin_of 0 1))
in let h₂ : ⟦C : coproduct C (λ (i : I), pullback C (f↗→(h i)↗→↗)) →→ coproduct C factors⟧
         := coproduct.univ C (λ (i : I), pullback C (f↗→(h i)↗→↗)) ccone₂
in let ccone₃ : CoProductCone C (λ (i : I), pullback C (f↗→(h i)↗→↗))
          := CoProductCone.mk y (λ i, f ∘∘ pullback.π C (f↗→(h i)↗→↗) (@fin_of 1 0))
in pullback.univ C (f ↗→ coproduct.univ C factors (CoProductCone.mk y h) ↗→↗)
    (PullbackCone.mk (f ↗→ coproduct.univ C factors (CoProductCone.mk y h) ↗→↗)
      (coproduct C (λ (i : I), pullback C (f ↗→ h i ↗→↗)))
      (coproduct.univ C (λ (i : I), pullback C (f↗→(h i)↗→↗)) ccone₃)
      (h₁ ↗← h₂ ↗←↗)
      begin
        apply HomsList.eq,
        { apply eq.symm,
          apply coproduct.univ.uniq C (λ (i : I), pullback C (f↗→(h i)↗→↗)) ccone₃,
          intro i,
          apply eq.symm, apply eq.trans (eq.symm C^.circ_assoc),
          apply Cat.circ.congr_right,
          apply eq.symm,
          apply coproduct.univ.mediates C (λ (i : I), pullback C (f↗→(h i)↗→↗)) ccone₁
        },
        apply HomsList.eq,
        { apply eq.symm,
          apply coproduct.univ.uniq C (λ (i : I), pullback C (f↗→(h i)↗→↗)) ccone₃,
          intro i,
          apply eq.symm, apply eq.trans (eq.symm C^.circ_assoc),
          apply eq.trans (Cat.circ.congr_right (eq.symm (coproduct.univ.mediates C (λ (i : I), pullback C (f↗→(h i)↗→↗)) ccone₂ i))),
          apply eq.trans C^.circ_assoc,
          apply eq.trans (Cat.circ.congr_left (eq.symm (coproduct.univ.mediates C factors (CoProductCone.mk y h) i))),
          dsimp [CoProductCone.mk, ProductCone.mk],
          apply pullback.π_comm C (f↗→(h i)↗→↗) (@fin_of 0 1) (@fin_of 1 0)
        },
        trivial
      end)

/-! #brief A category where pullbacks and coproducts commute.
-/
class HasStable_CoProduct_Pullback (C : Cat.{ℓobj ℓhom})
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasAllCoProducts : HasAllCoProducts C]
:= (inv : ∀ {x y : C^.obj} (f : C^.hom x y)
            {I : Type ℓ}
            (factors : I → C^.obj)
            (h : ∀ (i : I), C^.hom (factors i) y)
          , C^.hom (pullback C (f ↗→ coproduct.univ C factors (CoProductCone.mk y h) ↗→↗))
                   (coproduct C (λ (i : I), pullback C (f ↗→ h i ↗→↗))))
   (iso : ∀ {x y : C^.obj} (f : C^.hom x y)
            {I : Type ℓ}
            (factors : I → C^.obj)
            (h : ∀ (i : I), C^.hom (factors i) y)
          , Iso (coproduct_pullback.pullback_coproduct f factors h)
                (inv f factors h))

/-! #brief The hom A × Σ B → Σ (A × B).
-/
definition pullback_coproduct.coproduct_pullback {C : Cat.{ℓobj ℓhom}}
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasAllCoProducts : HasAllCoProducts C]
    [C_HasStable_CoProduct_Pullback : HasStable_CoProduct_Pullback C]
    {x y : C^.obj} (f : C^.hom x y)
    {I : Type ℓ}
    (factors : I → C^.obj)
    (h : ∀ (i : I), C^.hom (factors i) y)
    : C^.hom (pullback C (f ↗→ coproduct.univ C factors (CoProductCone.mk y h) ↗→↗))
             (coproduct C (λ (i : I), pullback C (f ↗→ h i ↗→↗)))
:= HasStable_CoProduct_Pullback.inv
    C_HasAllPullbacks
    C_HasAllCoProducts
    f factors h

/-! #brief The iso Σ (A × B) ≅ A × Σ B.
-/
definition coproduct_pullback.iso {C : Cat.{ℓobj ℓhom}}
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasAllCoProducts : HasAllCoProducts C]
    [C_HasStable_CoProduct_Pullback : HasStable_CoProduct_Pullback C]
    {x y : C^.obj} (f : C^.hom x y)
    {I : Type ℓ}
    (factors : I → C^.obj)
    (h : ∀ (i : I), C^.hom (factors i) y)
    : Iso (coproduct_pullback.pullback_coproduct f factors h)
          (pullback_coproduct.coproduct_pullback f factors h)
:= HasStable_CoProduct_Pullback.iso
    C_HasAllPullbacks
    C_HasAllCoProducts
    f factors h

end qp
