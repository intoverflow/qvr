/- -----------------------------------------------------------------------
Dependent products in LeanCat.
----------------------------------------------------------------------- -/

import ..c1_basic
import ..c2_limits
import ..c3_wtypes

namespace qp

open stdaux

universe variables ℓ


/- -----------------------------------------------------------------------
The dependent product functor.
----------------------------------------------------------------------- -/

/-! #brief The dependent product functor on objects.
-/
definition LeanCat.DepProdFun.obj {T₀ T₁ : LeanCat.{ℓ}^.obj}
    (disp : LeanCat.{ℓ}^.hom T₀ T₁)
    (S : OverObj LeanCat.{ℓ} T₀)
    : OverObj LeanCat.{ℓ} T₁
:= { obj := Σ (t₁ : T₁)
            , ∀ (t₀ : {t₀ : T₀ // disp t₀ = t₁})
              , { x : S^.obj // S^.hom x = t₀^.val}
   , hom := sigma.fst
   }

/-! #brief The dependent product functor on functions.
-/
definition LeanCat.DepProdFun.hom {T₀ T₁ : LeanCat.{ℓ}^.obj}
    (disp : LeanCat.{ℓ}^.hom T₀ T₁)
    {S₀ S₁ : OverObj LeanCat.{ℓ} T₀}
    (f : OverHom LeanCat.{ℓ} T₀ S₀ S₁)
    : OverHom LeanCat.{ℓ} T₁
       (@LeanCat.DepProdFun.obj T₀ T₁ disp S₀)
       (@LeanCat.DepProdFun.obj T₀ T₁ disp S₁)
:= let t₁ : (LeanCat.DepProdFun.obj disp S₀)^.obj → T₁
        := λ σ
           , σ^.fst
in let s₁ : ∀ (σ : (LeanCat.DepProdFun.obj disp S₀)^.obj)
              (t₀ : {t₀ // disp t₀ = t₁ σ})
            , S₁^.obj
         := λ σ t₀
            , f^.hom (σ^.snd t₀)^.val
in let ωs₁ : ∀ (σ : (LeanCat.DepProdFun.obj disp S₀)^.obj)
               (t₀ : {t₀ // disp t₀ = t₁ σ})
             , S₁^.hom (s₁ σ t₀) = t₀^.val
          := λ σ t₀
             , begin
                 apply eq.trans (congr_fun (eq.symm f^.triangle) (σ^.snd t₀)),
                 apply (σ^.snd t₀)^.property
               end
in { hom
      := λ σ, { fst := t₁ σ
              , snd := λ t₀, { val := s₁ σ t₀, property := ωs₁ σ t₀ }
              }
   , triangle := rfl
   }

/-! #brief The dependent product functor preserves identity functions.
-/
definition LeanCat.DepProdFun.hom_id {T₀ T₁ : LeanCat.{ℓ}^.obj}
    (disp : LeanCat.{ℓ}^.hom T₀ T₁)
    (S : OverObj LeanCat.{ℓ} T₀)
    : LeanCat.DepProdFun.hom disp (OverHom.id LeanCat.{ℓ} T₀ S)
       = OverHom.id LeanCat.{ℓ} T₁ (LeanCat.DepProdFun.obj disp S)
:= begin
     apply OverHom.eq,
     apply funext, intro σ,
     cases σ with t₁ f,
     apply congr_arg (sigma.mk t₁),
     apply funext, intro t₀,
     apply subtype.eq,
     trivial
   end

/-! #brief The dependent product functor distributes over composition.
-/
definition LeanCat.DepProdFun.hom_comp {T₀ T₁ : LeanCat.{ℓ}^.obj}
    (disp : LeanCat.{ℓ}^.hom T₀ T₁)
    (S₁ S₂ S₃ : OverObj LeanCat.{ℓ} T₀)
    (g : OverHom LeanCat.{ℓ} T₀ S₂ S₃)
    (f : OverHom LeanCat.{ℓ} T₀ S₁ S₂)
    : LeanCat.DepProdFun.hom disp (OverHom.comp LeanCat.{ℓ} T₀ _ _ _ g f)
       = OverHom.comp LeanCat.{ℓ} T₁ _ _ _ (LeanCat.DepProdFun.hom disp g) (LeanCat.DepProdFun.hom disp f)
:= begin
     apply OverHom.eq,
     apply funext, intro σ,
     cases σ with t₁ h,
     apply congr_arg (sigma.mk t₁),
     apply funext, intro t₀,
     apply subtype.eq,
     trivial
   end


/-! #brief The dependent product functor.
-/
definition LeanCat.DepProdFun {T₀ T₁ : LeanCat.{ℓ}^.obj}
    (disp : LeanCat.{ℓ}^.hom T₀ T₁)
    : Fun (OverCat LeanCat.{ℓ} T₀) (OverCat LeanCat.{ℓ} T₁)
:= { obj := LeanCat.DepProdFun.obj disp
   , hom := @LeanCat.DepProdFun.hom T₀ T₁ disp
   , hom_id := LeanCat.DepProdFun.hom_id disp
   , hom_circ := LeanCat.DepProdFun.hom_comp disp
   }

end qp
