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
definition LeanCat.DepProdFun.obj {B A : LeanCat.{ℓ}^.obj}
    (disp : LeanCat.{ℓ}^.hom B A)
    (S : OverObj LeanCat.{ℓ} B)
    : OverObj LeanCat.{ℓ} A
:= { obj := Σ (a : A)
            , ∀ (b : {b : B // disp b = a})
              , { x : S^.obj // S^.hom x = b^.val}
   , hom := sigma.fst
   }

/-! #brief The dependent product functor on functions.
-/
definition LeanCat.DepProdFun.hom {B A : LeanCat.{ℓ}^.obj}
    (disp : LeanCat.{ℓ}^.hom B A)
    {S₀ S₁ : OverObj LeanCat.{ℓ} B}
    (f : OverHom LeanCat.{ℓ} B S₀ S₁)
    : OverHom LeanCat.{ℓ} A
       (@LeanCat.DepProdFun.obj B A disp S₀)
       (@LeanCat.DepProdFun.obj B A disp S₁)
:= let a : (LeanCat.DepProdFun.obj disp S₀)^.obj → A
        := λ σ
           , σ^.fst
in let s₁ : ∀ (σ : (LeanCat.DepProdFun.obj disp S₀)^.obj)
              (b : {b // disp b = a σ})
            , S₁^.obj
         := λ σ b
            , f^.hom (σ^.snd b)^.val
in let ωs₁ : ∀ (σ : (LeanCat.DepProdFun.obj disp S₀)^.obj)
               (b : {b // disp b = a σ})
             , S₁^.hom (s₁ σ b) = b^.val
          := λ σ b
             , begin
                 apply eq.trans (congr_fun (eq.symm f^.triangle) (σ^.snd b)),
                 apply (σ^.snd b)^.property
               end
in { hom
      := λ σ, { fst := a σ
              , snd := λ b, { val := s₁ σ b, property := ωs₁ σ b }
              }
   , triangle := rfl
   }

/-! #brief The dependent product functor preserves identity functions.
-/
definition LeanCat.DepProdFun.hom_id {B A : LeanCat.{ℓ}^.obj}
    (disp : LeanCat.{ℓ}^.hom B A)
    (S : OverObj LeanCat.{ℓ} B)
    : LeanCat.DepProdFun.hom disp (OverHom.id LeanCat.{ℓ} B S)
       = OverHom.id LeanCat.{ℓ} A (LeanCat.DepProdFun.obj disp S)
:= begin
     apply OverHom.eq,
     apply funext, intro σ,
     cases σ with a f,
     apply congr_arg (sigma.mk a),
     apply funext, intro b,
     apply subtype.eq,
     trivial
   end

/-! #brief The dependent product functor distributes over composition.
-/
definition LeanCat.DepProdFun.hom_comp {B A : LeanCat.{ℓ}^.obj}
    (disp : LeanCat.{ℓ}^.hom B A)
    (S₁ S₂ S₃ : OverObj LeanCat.{ℓ} B)
    (g : OverHom LeanCat.{ℓ} B S₂ S₃)
    (f : OverHom LeanCat.{ℓ} B S₁ S₂)
    : LeanCat.DepProdFun.hom disp (OverHom.comp LeanCat.{ℓ} B _ _ _ g f)
       = OverHom.comp LeanCat.{ℓ} A _ _ _ (LeanCat.DepProdFun.hom disp g) (LeanCat.DepProdFun.hom disp f)
:= begin
     apply OverHom.eq,
     apply funext, intro σ,
     cases σ with a h,
     apply congr_arg (sigma.mk a),
     apply funext, intro b,
     apply subtype.eq,
     trivial
   end


/-! #brief The dependent product functor.
-/
definition LeanCat.DepProdFun {B A : LeanCat.{ℓ}^.obj}
    (disp : LeanCat.{ℓ}^.hom B A)
    : Fun (OverCat LeanCat.{ℓ} B) (OverCat LeanCat.{ℓ} A)
:= { obj := LeanCat.DepProdFun.obj disp
   , hom := @LeanCat.DepProdFun.hom B A disp
   , hom_id := LeanCat.DepProdFun.hom_id disp
   , hom_circ := LeanCat.DepProdFun.hom_comp disp
   }

end qp
