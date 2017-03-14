/- -----------------------------------------------------------------------
Natural transformations.
----------------------------------------------------------------------- -/

import .s2_functors

namespace qp

open stdaux

universe variables ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂ ℓobj₃ ℓhom₃ ℓobj₄ ℓhom₄

/-! #brief A natural transformation between functors.
-/
structure NatTrans
    {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    (F G : Fun C D)
    : Type (max ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂)
:= (com : ∀ (x : C^.obj), D^.hom (F^.obj x) (G^.obj x))
   (natural : ∀ {x y : C^.obj} {f : C^.hom x y}
              , D^.circ (com y) (F^.hom f)
                 = D^.circ (G^.hom f) (com x))

-- A natural transformation.
-- \rightarrowtail
notation F `↣` G := NatTrans F G

/-! #brief Equality of natural transformations.
-/
theorem NatTrans.eq
    {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F₁ F₂ : Fun C D}
    : ∀ {η₁ η₂ : NatTrans F₁ F₂}
         (ω : η₁^.com = η₂^.com)
      , η₁ = η₂
| (NatTrans.mk com ω₁) (NatTrans.mk .com ω₂) (eq.refl .com) := rfl

/-! #brief Heterogeneous equality of natural transformations.
-/
theorem NatTrans.heq
    {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    : ∀ {F₁₁ F₁₂ F₂₁ F₂₂ : Fun C D}
         {η₁ : NatTrans F₁₁ F₁₂}
         {η₂ : NatTrans F₂₁ F₂₂}
         (ω₁ : F₁₁ = F₂₁)
         (ω₂ : F₁₂ = F₂₂)
         (ωcom : F₁₁ = F₂₁ → F₁₂ = F₂₂ → η₁^.com == η₂^.com)
       , η₁ == η₂
| F₁ F₂ .F₁ .F₂ η₁ η₂ (eq.refl .F₁) (eq.refl .F₂) ωcom
:= heq_of_eq (NatTrans.eq (eq_of_heq (ωcom rfl rfl)))
         

/- -----------------------------------------------------------------------
Natural transformations are morphisms of functors.
----------------------------------------------------------------------- -/

/-! #brief The identity natural transformation.
-/
definition NatTrans.id {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    (F : Fun C D)
    : NatTrans F F
:= { com := λ x, D^.id (F^.obj x)
   , natural := λ x y f, by rw [D^.circ_id_left, D^.circ_id_right]
   }

/-! #brief Composition of natural transformations.
-/
definition NatTrans.comp {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F₁ F₂ F₃ : Fun C D}
    (η₂₃ : NatTrans F₂ F₃)
    (η₁₂ : NatTrans F₁ F₂)
    : NatTrans F₁ F₃
:= { com := λ x, D^.circ (η₂₃^.com x) (η₁₂^.com x)
   , natural := λ x y f
                , by calc η₂₃^.com y ∘∘ η₁₂^.com y ∘∘ F₁^.hom f
                              = η₂₃^.com y ∘∘ (η₁₂^.com y ∘∘ F₁^.hom f) : by rw D^.circ_assoc
                          ... = η₂₃^.com y ∘∘ (F₂^.hom f ∘∘ η₁₂^.com x) : by rw η₁₂^.natural
                          ... = (η₂₃^.com y ∘∘ F₂^.hom f) ∘∘ η₁₂^.com x : by rw D^.circ_assoc
                          ... = (F₃^.hom f ∘∘ η₂₃^.com x) ∘∘ η₁₂^.com x : by rw η₂₃^.natural
                          ... = F₃^.hom f ∘∘ (η₂₃^.com x ∘∘ η₁₂^.com x) : by rw D^.circ_assoc
   }

-- Composition of natural transformations.
-- \Diamond\Diamond
infixl `◇◇` : 150 := NatTrans.comp

/-! #brief Composition of natural transformations is associative.
-/
theorem NatTrans.comp_assoc {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    (F₁ F₂ F₃ F₄ : Fun C D)
    (η₃₄ : NatTrans F₃ F₄)
    (η₂₃ : NatTrans F₂ F₃)
    (η₁₂ : NatTrans F₁ F₂)
    : NatTrans.comp η₃₄ (NatTrans.comp η₂₃ η₁₂)
       = NatTrans.comp (NatTrans.comp η₃₄ η₂₃) η₁₂
:= NatTrans.eq (funext (λ c, D^.circ_assoc))

/-! #brief Left-identity for composition of natural transformation.
-/
theorem NatTrans.comp_id_left {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F₁ F₂ : Fun C D}
    (η : NatTrans F₁ F₂)
    : NatTrans.comp (NatTrans.id F₂) η = η
:= NatTrans.eq (funext (λ c, D^.circ_id_left))

/-! #brief Right-identity for composition of natural transformation.
-/
theorem NatTrans.comp_id_right {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F₁ F₂ : Fun C D}
    (η : NatTrans F₁ F₂)
    : NatTrans.comp η (NatTrans.id F₁) = η
:= NatTrans.eq (funext (λ c, D^.circ_id_right))



/- -----------------------------------------------------------------------
Functor categories.
----------------------------------------------------------------------- -/

/-! #brief A functor category.
-/
definition FunCat (C : Cat.{ℓobj₁ ℓhom₁}) (D : Cat.{ℓobj₂ ℓhom₂})
    : Cat
:= { obj := Fun C D
   , hom := NatTrans
   , id := NatTrans.id
   , circ := @NatTrans.comp C D
   , circ_assoc := @NatTrans.comp_assoc C D
   , circ_id_left := @NatTrans.comp_id_left C D
   , circ_id_right := @NatTrans.comp_id_right C D
   }



/- -----------------------------------------------------------------------
Whisker composition of natural transformations.
----------------------------------------------------------------------- -/

/-! #brief Left whisker composition.
-/
definition NatTrans.whisk_left {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    (G : Fun C D)
    {F₁ F₂ : Fun B C}
    (η : NatTrans F₁ F₂)
    : NatTrans (Fun.comp G F₁) (Fun.comp G F₂)
:= { com := λ b, G^.hom (η^.com b)
   , natural := λ b₁ b₂ f
                , by calc G^.hom (η^.com b₂) ∘∘ (G □□ F₁)^.hom f
                              = G^.hom (η^.com b₂ ∘∘ F₁^.hom f)        : eq.symm G^.hom_circ
                          ... = G^.hom (F₂^.hom f ∘∘ η^.com b₁)        : by rw η^.natural
                          ... = (G □□ F₂)^.hom f ∘∘ G^.hom (η^.com b₁) : G^.hom_circ
   }

-- Left horizontal composition.
-- \Box\Diamond
infixr `□◇` : 150 := NatTrans.whisk_left

/-! #brief Left whisker composition and identity functors.
-/
theorem NatTrans.whisk_left.id_left {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F₁ F₂ : Fun C D}
    {η : NatTrans F₁ F₂}
    : NatTrans.whisk_left (Fun.id D) η == η
:= NatTrans.heq Fun.comp_id_left Fun.comp_id_left
    (λ ω₁ ω₂, heq.refl _)

/-! #brief Left whisker composition and composition of functors.
-/
definition NatTrans.whisk_left.comp_left
    {A : Cat.{ℓobj₁ ℓhom₁}} {B : Cat.{ℓobj₂ ℓhom₂}} {C : Cat.{ℓobj₃ ℓhom₃}} {D : Cat.{ℓobj₄ ℓhom₄}}
    {H : Fun C D}
    {G : Fun B C}
    {F₁ F₂ : Fun A B}
    {η : NatTrans F₁ F₂}
    : NatTrans.whisk_left (Fun.comp H G) η == NatTrans.whisk_left H (NatTrans.whisk_left G η)
:= NatTrans.heq Fun.comp_assoc Fun.comp_assoc
    (λ ω₁ ω₂, heq.refl _)

/-! #brief Left whisker composition and identity natural transformations.
-/
theorem NatTrans.whisk_left.id_right {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    {G : Fun C D}
    {F : Fun B C}
    : NatTrans.whisk_left G (NatTrans.id F) = NatTrans.id (Fun.comp G F)
:= NatTrans.eq (funext (λ b, G^.hom_id))

/-! #brief Left whisker composition and composition of natural transformations.
-/
theorem NatTrans.whisk_left.comp_right {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    {G : Fun C D}
    {F₁ F₂ F₃ : Fun B C}
    {η₂₃ : NatTrans F₂ F₃}
    {η₁₂ : NatTrans F₁ F₂}
    : NatTrans.whisk_left G (NatTrans.comp η₂₃ η₁₂)
       = NatTrans.comp (NatTrans.whisk_left G η₂₃) (NatTrans.whisk_left G η₁₂)
:= NatTrans.eq (funext (λ b, G^.hom_circ))


/-! #brief Right whisker composition.
-/
definition NatTrans.whisk_right {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    {G₁ G₂ : Fun C D}
    (η : NatTrans G₁ G₂)
    (F : Fun B C)
    : NatTrans (Fun.comp G₁ F) (Fun.comp G₂ F)
:= { com := λ b, η^.com (F^.obj b)
   , natural := λ b₁ b₂ f, η^.natural
   }

-- Right horizontal composition.
-- \Diamond\Box
infixl `◇□` : 150 := NatTrans.whisk_right

end qp
