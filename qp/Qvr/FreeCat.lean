/- ----------------------------------------------------------------------------
Free categories.
---------------------------------------------------------------------------- -/

import .basic

namespace qp
universe variables ℓvtx ℓarr ℓvtx₁ ℓarr₁ ℓvtx₂ ℓarr₂ ℓvtx₃ ℓarr₃



/- ----------------------------------------------------------------------------
The free category generated by a quiver.
---------------------------------------------------------------------------- -/

/-! #brief A hom in a free category.
-/
inductive FreeCat.Hom {Q : Qvr.{ℓvtx ℓarr}}
    : ‖Q‖ → ‖Q‖ → Type (max ℓvtx ℓarr)
| id : ∀ (v : ‖Q‖), FreeCat.Hom v v
| step : ∀ (m n p : ‖Q‖) (e : Qvr.BxArr m n) (es : FreeCat.Hom n p)
         , FreeCat.Hom m p

-- A hom in a free category.
-- \leadsto\leadsto
notation v₁ `↝↝` v₂ := FreeCat.Hom v₁ v₂

/-! #brief Every boxed arrow can be regarded as a hom in the free category.
-/
@[reducible] instance Qvr.BxArr.has_coe_to_Hom {Q : Qvr.{ℓvtx ℓarr}} {v₁ v₂ : ‖Q‖}
    : has_coe (Qvr.BxArr v₁ v₂) (v₁ ↝↝ v₂)
:= { coe := λ be, FreeCat.Hom.step _ _ _ be (FreeCat.Hom.id _)
   }

/-! #brief Composition of homs in the free category.
-/
definition FreeCat.Hom.comp {Q : Qvr.{ℓvtx ℓarr}}
    : ∀ {x₁ x₂ x₃ : ‖Q‖}
        (w₂₃ : x₂ ↝↝ x₃) (w₁₂ : x₁ ↝↝ x₂)
      , x₁ ↝↝ x₃
| x₁ x₂ x₃ w₂₃ w₁₂
:= begin
     induction w₁₂,
     { exact w₂₃ },
     { exact FreeCat.Hom.step _ _ _ e (ih_1 w₂₃) }
   end

/-! #brief FreeCat.Hom.id is a right-identity for composition.
-/
@[simp] theorem FreeCat.Hom.comp_id_right {Q : Qvr.{ℓvtx ℓarr}}
    : ∀ {x₁ x₂ : ‖Q‖} {w₁₂ : x₁ ↝↝ x₂}
      , FreeCat.Hom.comp w₁₂ (FreeCat.Hom.id x₁) = w₁₂
| x₁ x₂ w₁₂ := rfl

/-! #brief Helper lemma for computing FreeCat.Hom.comp.
-/
@[simp] theorem FreeCat.Hom.comp.step {Q : Qvr.{ℓvtx ℓarr}}
    : ∀ {x₁ n x₂ x₃ : ‖Q‖} {w₂₃ : x₂ ↝↝ x₃}
        {e : Qvr.BxArr x₁ n} {es : n ↝↝ x₂}
      , FreeCat.Hom.comp w₂₃ (FreeCat.Hom.step x₁ n x₂ e es)
          = FreeCat.Hom.step x₁ n x₃ e (FreeCat.Hom.comp w₂₃ es)
| x₁ n x₂ x₃ w₂₃ e es := rfl

/-! #brief Composition of homs in the free category is associative.
-/
@[simp] theorem FreeCat.Hom.comp_assoc {Q : Qvr.{ℓvtx ℓarr}}
    : ∀ {x₁ x₂ x₃ x₄ : ‖Q‖}
        {w₃₄ : x₃ ↝↝ x₄} {w₂₃ : x₂ ↝↝ x₃} {w₁₂ : x₁ ↝↝ x₂}
      , FreeCat.Hom.comp w₃₄ (FreeCat.Hom.comp w₂₃ w₁₂)
         = FreeCat.Hom.comp (FreeCat.Hom.comp w₃₄ w₂₃) w₁₂
| x₁ x₂ x₃ x₄ w₃₄ w₂₃ w₁₂
:= begin
     induction w₁₂,
     { simp },
     { simp, rw (ih_1 w₂₃) }
   end

/-! #brief FreeCat.Hom.id is a left-identity for composition.
-/
@[simp] theorem FreeCat.Hom.comp_id_left {Q : Qvr.{ℓvtx ℓarr}}
    : ∀ {x₁ x₂ : ‖Q‖} {w₁₂ : x₁ ↝↝ x₂}
      , FreeCat.Hom.comp (FreeCat.Hom.id x₂) w₁₂ = w₁₂
| x₁ x₂ w₁₂
:= begin
     induction w₁₂,
     { simp },
     { simp, rw ih_1 }
   end

/-! #brief The free category generated by a quiver.
-/
@[reducible] definition FreeCat (Q : Qvr.{ℓvtx ℓarr})
    : Cat.{ℓvtx ((max ℓvtx ℓarr) + 1)}
:= { obj := ‖Q‖
   , hom := λ v₁ v₂, v₁ ↝↝ v₂
   , id := FreeCat.Hom.id
   , circ := @FreeCat.Hom.comp Q
   , circ_assoc := @FreeCat.Hom.comp_assoc Q
   , circ_id_left := @FreeCat.Hom.comp_id_left Q
   , circ_id_right := @FreeCat.Hom.comp_id_right Q
   }



/- ----------------------------------------------------------------------------
The free functor generated by a quiver morphism.
---------------------------------------------------------------------------- -/

/-! #brief Action of a quiver morphism on a hom in the free category.
-/
definition Qvr.Mor.on_Hom {Q₁ : Qvr.{ℓvtx₁ ℓarr₁}} {Q₂ : Qvr.{ℓvtx₂ ℓarr₂}}
    (M : Q₁ ⇒⇒ Q₂)
    : ∀ {x₁ x₂ : ‖Q₁‖}
        (w : FreeCat.Hom x₁ x₂)
      , FreeCat.Hom (M x₁) (M x₂)
| x₁ x₂ w
:= begin
     induction w,
     { apply FreeCat.Hom.id },
     { apply FreeCat.Hom.step _ _ _ (M □↘ e) ih_1 }
   end

/-! #brief Simplification lemma for Qvr.Mor.on_Hom.
-/
@[simp] theorem Qvr.Mor.on_Hom.id {Q₁ : Qvr.{ℓvtx₁ ℓarr₁}} {Q₂ : Qvr.{ℓvtx₂ ℓarr₂}}
    (M : Q₁ ⇒⇒ Q₂)
    {v : ‖Q₁‖}
    : Qvr.Mor.on_Hom M (FreeCat.Hom.id v) = FreeCat.Hom.id (M v)
:= rfl

/-! #brief Simplification lemma for Qvr.Mor.on_Hom.
-/
@[simp] theorem Qvr.Mor.on_Hom.step {Q₁ : Qvr.{ℓvtx₁ ℓarr₁}} {Q₂ : Qvr.{ℓvtx₂ ℓarr₂}}
    (M : Q₁ ⇒⇒ Q₂)
    {x₁ x₂ x₃ : ‖Q₁‖} {e : Qvr.BxArr x₁ x₂} {es : x₂ ↝↝ x₃}
    : Qvr.Mor.on_Hom M (FreeCat.Hom.step x₁ x₂ x₃ e es)
       = FreeCat.Hom.step (M x₁) (M x₂) (M x₃) (M □↘ e) (Qvr.Mor.on_Hom M es)
:= rfl

/-! #brief The free functor generated by a quiver morphism.
-/
@[reducible] definition FreeCat.FreeFun {Q₁ : Qvr.{ℓvtx₁ ℓarr₁}} {Q₂ : Qvr.{ℓvtx₂ ℓarr₂}}
    (M : Q₁ ⇒⇒ Q₂)
    : FreeCat Q₁ ⇉⇉ FreeCat Q₂
:= { obj := M^.vtx
   , hom := λ x y w, Qvr.Mor.on_Hom M w
   , hom_id := λ x, Qvr.Mor.on_Hom.id M
   , hom_circ
      := λ x₁ x₂ x₃ g f
         , begin
             dsimp at f,
             induction f,
             { apply rfl },
             { simp, rw ih_1 }
           end
   }

/-! #brief FreeCat.FreeFun maps the identity morphism to the identity functor.
-/
@[simp] theorem FreeCat.FreeFun.id {Q : Qvr.{ℓvtx ℓarr}}
    : FreeCat.FreeFun (Qvr.Mor.id Q) = Fun.id (FreeCat Q)
:= begin
     apply Fun.eq,
     { intro x, apply rfl },
     { intros x y w,
       dsimp,
       dsimp at w,
       induction w,
       { apply heq.refl },
       { dsimp, rw (eq_of_heq ih_1), cases e, apply heq.refl }
     }
   end

/-! #brief FreeCat.FreeFun distributes over composition.
-/
@[simp] theorem FreeCat.FreeFun.comp {Q₁ : Qvr.{ℓvtx₁ ℓarr₁}} {Q₂ : Qvr.{ℓvtx₂ ℓarr₂}} {Q₃ : Qvr.{ℓvtx₃ ℓarr₃}}
      (N : Q₂ ⇒⇒ Q₃) (M : Q₁ ⇒⇒ Q₂)
    : FreeCat.FreeFun (N ◯◯ M) = FreeCat.FreeFun N □□ FreeCat.FreeFun M
:= begin
     apply Fun.eq,
     { intro x, apply rfl },
     {
       intros x y w,
       dsimp at w,
       induction w,
       { apply heq.refl },
       { exact sorry } -- dsimp [FreeCat.FreeFun], dsimp at ih_1, rw (eq_of_heq ih_1), apply rfl }
     }
   end



/- ----------------------------------------------------------------------------
The free category functor.
---------------------------------------------------------------------------- -/

/-! #brief The free category functor.
-/
@[reducible] definition FreeCatFun
    : QvrCat.{ℓvtx ℓarr} ⇉⇉ CatCat.{ℓvtx ((max ℓvtx ℓarr) + 1)}
:= { obj := FreeCat
   , hom := @FreeCat.FreeFun
   , hom_id := @FreeCat.FreeFun.id
   , hom_circ := @FreeCat.FreeFun.comp
   }

end qp
