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
   (natural : ∀ {x y : C^.obj} (f : C^.hom x y)
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
| (NatTrans.mk com ω₁) (NatTrans.mk .(com) ω₂) (eq.refl .(com)) := rfl

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
| F₁ F₂ .(F₁) .(F₂) η₁ η₂ (eq.refl .(F₁)) (eq.refl .(F₂)) ωcom
:= heq_of_eq (NatTrans.eq (eq_of_heq (ωcom rfl rfl)))

/-! #brief Congruence for NatTrans.com
-/
theorem NatTrans.congr_com
    {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F₁ F₂ : Fun C D}
    : ∀ {η₁ η₂ : NatTrans F₁ F₂}
        (ωη : η₁ = η₂)
        {c : C^.obj}
      , η₁^.com c = η₂^.com c
| η .(η) (eq.refl .(η)) c := rfl



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
infixl ` ◇◇ ` : 150 := NatTrans.comp

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

/-! #brief The casting natural transformation.
-/
definition NatTrans.cast {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    : ∀ {F₁ F₂ : Fun C D}
        (ωF : F₁ = F₂)
      , NatTrans F₁ F₂
| F .(F) (eq.refl .(F)) := NatTrans.id F

/-! #brief The casting transformation is the identity.
-/
theorem NatTrans.simp_cast {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    : ∀ {F₁ F₂ : Fun C D}
        {ωF : F₁ = F₂}
      , NatTrans.cast ωF == NatTrans.id F₁
| F .(F) (eq.refl .(F)) := heq.refl _

/-! #brief The casting transformation has identity components.
-/
theorem NatTrans.cast.com {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    : ∀ {F₁ F₂ : Fun C D}
        {ωF : F₁ = F₂}
        {c : C^.obj}
      , (NatTrans.cast ωF)^.com c = cast_hom (by rw ωF)
| F .(F) (eq.refl .(F)) c := rfl

/-! #brief Composition of casting natural transformations.
-/
theorem NatTrans.comp_cast {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    : ∀ {F₁ F₂ F₃ : Fun C D}
        {ωF₁₂ : F₁ = F₂}
        {ωF₂₃ : F₂ = F₃}
      , NatTrans.comp (NatTrans.cast ωF₂₃) (NatTrans.cast ωF₁₂)
         = NatTrans.cast (eq.trans ωF₁₂ ωF₂₃)
| F .(F) .(F) (eq.refl .(F)) (eq.refl .(F))
:= NatTrans.eq (funext (λ c, D^.circ_id_left))

/-! #brief Casting natural transformations are just identities.
-/
theorem NatTrans.cast_rfl {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F : Fun C D}
    : NatTrans.cast (eq.refl F) = NatTrans.id F
:= rfl



/- -----------------------------------------------------------------------
Constant transformations.
----------------------------------------------------------------------- -/

/-! #brief A constant transformation.
-/
definition ConstTrans (C : Cat.{ℓobj₁ ℓhom₁}) {D : Cat.{ℓobj₂ ℓhom₂}}
    {d₁ d₂ : D^.obj} (h : D^.hom d₁ d₂)
    : NatTrans (ConstFun C d₁) (ConstFun C d₂)
:= { com := λ c, h
   , natural := λ c₁ c₂ f, eq.trans D^.circ_id_right (eq.symm D^.circ_id_left)
   }



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

/-! #brief A presheaf category.
-/
definition PreShCat (C : Cat.{ℓobj₁ ℓhom₁})
    : Cat.{(max ℓobj₁ (ℓhom₁ + 1)) ((max ℓobj₁ (ℓhom₁ + 1)) + 1)}
:= FunCat (OpCat C) LeanCat.{ℓhom₁}

/-! #brief Functor categories have pointwise final objects.
-/
definition FunCat.HasFinal {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    [D_HasFinal : HasFinal D]
    : HasFinal (FunCat C D)
:= HasFinal.show (ConstFun C (final D))
    (λ F, { com := λ c, final_hom (F^.obj c)
          , natural
             := λ c₁ c₂ f
                , eq.trans (final_hom.uniq D) (eq.symm D^.circ_id_left)
          })
    (λ F η, NatTrans.eq (funext (λ c, final_hom.uniq D)))

/-! #brief Functor categories have pointwise initial objects.
-/
definition FunCat.HasInit {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    [D_HasInit : HasInit D]
    : HasInit (FunCat C D)
:= HasFinal.show (ConstFun C (init D))
    (λ F, { com := λ c, init_hom (F^.obj c)
          , natural
             := λ c₁ c₂ f
                , eq.trans D^.circ_id_right (eq.symm (init_hom.uniq D))
          })
    (λ F η, NatTrans.eq (funext (λ c, init_hom.uniq D)))

/- -----------------------------------------------------------------------
Swapping the arguments of functors into functor categories.
----------------------------------------------------------------------- -/

/-! #brief Swap the arguments of a functor.
-/
definition Fun.swap.obj {A : Cat.{ℓobj₁ ℓhom₁}} {B : Cat.{ℓobj₂ ℓhom₂}} {C : Cat.{ℓobj₃ ℓhom₃}}
    (F : Fun A (FunCat B C))
    (b : B^.obj)
    : Fun A C
:= { obj := λ a, (F^.obj a)^.obj b
   , hom := λ a₁ a₂ f, (F^.hom f)^.com b
   , hom_id := λ x, begin
                      rw F^.hom_id,
                      trivial
                    end
   , hom_circ := λ x y z g f, begin rw F^.hom_circ, trivial end
   }

/-! #brief Swap the arguments of a natural transformation.
-/
definition Fun.swap.hom {A : Cat.{ℓobj₁ ℓhom₁}} {B : Cat.{ℓobj₂ ℓhom₂}} {C : Cat.{ℓobj₃ ℓhom₃}}
    (F : Fun A (FunCat B C))
    (b₁ b₂ : B^.obj) (f : B^.hom b₁ b₂)
    : NatTrans (Fun.swap.obj F b₁) (Fun.swap.obj F b₂)
:= { com := λ a, (F^.obj a)^.hom f
   , natural := λ x y g, eq.symm ((F^.hom g)^.natural f)
   }


/-! #brief Swap the arguments.
-/
definition Fun.swap {A : Cat.{ℓobj₁ ℓhom₁}} {B : Cat.{ℓobj₂ ℓhom₂}} {C : Cat.{ℓobj₃ ℓhom₃}}
    (F : Fun A (FunCat B C))
    : Fun B (FunCat A C)
:= { obj := Fun.swap.obj F
   , hom := Fun.swap.hom F
   , hom_id := λ b, NatTrans.eq (funext (λ a, (F^.obj a)^.hom_id))
   , hom_circ := λ b₁ b₂ b₃ g f, NatTrans.eq (funext (λ a, (F^.obj a)^.hom_circ))
   }



/- -----------------------------------------------------------------------
Natural isomorphisms.
----------------------------------------------------------------------- -/

/-! #brief A natural isomorphism between two functors.
-/
definition NatIso {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F₁ F₂ : Fun C D}
    (η₁₂ : NatTrans F₁ F₂)
    (η₂₁ : NatTrans F₂ F₁)
    : Prop
:= @Iso (FunCat C D) F₁ F₂ η₁₂ η₂₁

/-! #brief The identity natural transformation is a natural isomorphism.
-/
theorem NatIso.id {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F : Fun C D}
    : NatIso (NatTrans.id F) (NatTrans.id F)
:= Cat.id.Iso F

/-! #brief The composition of two natural isomorphisms is a natural iso.
-/
theorem NatIso.comp {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F₁ F₂ F₃ : Fun C D}
    {η₂₃ : NatTrans F₂ F₃} {η₂₃' : NatTrans F₃ F₂} (iso₂₃ : NatIso η₂₃ η₂₃')
    {η₁₂ : NatTrans F₁ F₂} {η₁₂' : NatTrans F₂ F₁} (iso₁₂ : NatIso η₁₂ η₁₂')
    : NatIso (NatTrans.comp η₂₃ η₁₂) (NatTrans.comp η₁₂' η₂₃')
:= Cat.circ.Iso iso₂₃ iso₁₂

/-! #brief The components of a natural isomorphism are isomorphisms.
-/
theorem NatIso.com {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F₁ F₂ : Fun C D}
    {η₁₂ : NatTrans F₁ F₂}
    {η₂₁ : NatTrans F₂ F₁}
    (iso : NatIso η₁₂ η₂₁)
    (c : C^.obj)
    : Iso (η₁₂^.com c) (η₂₁^.com c)
:= { id₁ := congr_arg (λ η, NatTrans.com η c) iso^.id₁
   , id₂ := congr_arg (λ η, NatTrans.com η c) iso^.id₂
   }

/-! #brief A natural transformation whose components are isos is a natural iso.
-/
theorem NatTrans.Iso_on_com {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F₁ F₂ : Fun C D}
    {η₁₂ : NatTrans F₁ F₂}
    {η₂₁ : NatTrans F₂ F₁}
    (ω : ∀ (c : C^.obj), Iso (η₁₂^.com c) (η₂₁^.com c))
    : NatIso η₁₂ η₂₁
:= { id₁ := NatTrans.eq (funext (λ c, (ω c)^.id₁))
   , id₂ := NatTrans.eq (funext (λ c, (ω c)^.id₂))
   }



/- -----------------------------------------------------------------------
Opposite transformations.
----------------------------------------------------------------------- -/

/-! #brief An opposite transformation.
-/
definition OpTrans {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F₁ F₂ : Fun C D}
    (η : NatTrans F₁ F₂)
    : NatTrans (OpFun F₂) (OpFun F₁)
:= { com := λ x, η^.com x
   , natural := λ x y f, eq.symm (η^.natural f)
   }

/-! #brief Opposites of natural isos are again natural isos.
-/
definition OpNatIso {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F₁ F₂ : Fun C D}
    {η₁₂ : NatTrans F₁ F₂}
    {η₂₁ : NatTrans F₂ F₁}
    (η_iso : NatIso η₁₂ η₂₁)
    : NatIso (OpTrans η₁₂) (OpTrans η₂₁)
:= { id₁ := begin
              apply NatTrans.eq, apply funext, intro c,
              apply NatTrans.congr_com η_iso^.id₂
            end
   , id₂ := begin
              apply NatTrans.eq, apply funext, intro c,
              apply NatTrans.congr_com η_iso^.id₁
            end
   }



/- -----------------------------------------------------------------------
Monics.
----------------------------------------------------------------------- -/

/-! #brief Monic natural transformations have monic components.
-/
theorem NatTrans.com.Monic {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F₁ F₂ : Fun C D}
    {η : NatTrans F₁ F₂}
    (η_Monic : @Monic (FunCat C D) F₁ F₂ η)
    (c : C^.obj)
    : Monic (η^.com c)
:= Monic.show (λ d f₁ f₂ ω
               , begin exact sorry end)


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

-- Left whisker composition.
-- \Box\Diamond
infixr ` □◇ ` : 150 := NatTrans.whisk_left

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

/-! #brief Left whisker composition preserves natural isomorphisms.
-/
theorem NatTrans.whisk_left.NatIso {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    (G : Fun C D)
    {F₁ F₂ : Fun B C}
    {η₁₂ : NatTrans F₁ F₂}
    {η₂₁ : NatTrans F₂ F₁}
    (iso : NatIso η₁₂ η₂₁)
    : NatIso (NatTrans.whisk_left G η₁₂) (NatTrans.whisk_left G η₂₁)
:= NatTrans.Iso_on_com (λ b, Fun.preserves_Iso G (NatIso.com iso b))


/-! #brief Right whisker composition.
-/
definition NatTrans.whisk_right {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    {G₁ G₂ : Fun C D}
    (η : NatTrans G₁ G₂)
    (F : Fun B C)
    : NatTrans (Fun.comp G₁ F) (Fun.comp G₂ F)
:= { com := λ b, η^.com (F^.obj b)
   , natural := λ b₁ b₂ f, η^.natural _
   }

-- Right whisker composition.
-- \Diamond\Box
infixl ` ◇□ ` : 150 := NatTrans.whisk_right

/-! #brief Right whisker composition and identity functors.
-/
theorem NatTrans.whisk_right_id_right {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F₁ F₂ : Fun C D}
    {η : NatTrans F₁ F₂}
    : NatTrans.whisk_right η (Fun.id C) == η
:= NatTrans.heq Fun.comp_id_right Fun.comp_id_right
    (λ ω₁ ω₂, heq.refl _)

/-! #brief Right whisker composition and composition of functors.
-/
definition NatTrans.whisk_right.comp_right
    {A : Cat.{ℓobj₁ ℓhom₁}} {B : Cat.{ℓobj₂ ℓhom₂}} {C : Cat.{ℓobj₃ ℓhom₃}} {D : Cat.{ℓobj₄ ℓhom₄}}
    {F₁ F₂ : Fun C D}
    {η : NatTrans F₁ F₂}
    {H : Fun B C}
    {G : Fun A B}
    : NatTrans.whisk_right η (Fun.comp H G) == NatTrans.whisk_right (NatTrans.whisk_right η H) G
:= NatTrans.heq Fun.comp_assoc Fun.comp_assoc
    (λ ω₁ ω₂, heq.refl _)

/-! #brief Right whisker composition and identity natural transformations.
-/
theorem NatTrans.whisk_right.id_left {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    {G : Fun C D}
    {F : Fun B C}
    : NatTrans.whisk_right (NatTrans.id G) F = NatTrans.id (Fun.comp G F)
:= NatTrans.eq (funext (λ b, rfl))

/-! #brief Right whisker composition and composition of natural transformations.
-/
theorem NatTrans.whisk_right.comp_left {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    {G : Fun B C}
    {F₁ F₂ F₃ : Fun C D}
    {η₂₃ : NatTrans F₂ F₃}
    {η₁₂ : NatTrans F₁ F₂}
    : NatTrans.whisk_right (NatTrans.comp η₂₃ η₁₂) G
       = NatTrans.comp (NatTrans.whisk_right η₂₃ G) (NatTrans.whisk_right η₁₂ G)
:= NatTrans.eq (funext (λ b, rfl))

/-! #brief Right whisker composition preserves natural isomorphisms.
-/
theorem NatTrans.whisk_right.NatIso {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    {G₁ G₂ : Fun C D}
    {η₁₂ : NatTrans G₁ G₂}
    {η₂₁ : NatTrans G₂ G₁}
    (iso : NatIso η₁₂ η₂₁)
    (F : Fun B C)
    : NatIso (NatTrans.whisk_right η₁₂ F) (NatTrans.whisk_right η₂₁ F)
:= NatTrans.Iso_on_com (λ b, NatIso.com iso (F^.obj b))



/- -----------------------------------------------------------------------
Adjoint functors.
----------------------------------------------------------------------- -/

/-! #brief An adjunction between two functors.
-/
structure Adj
    {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    (L : Fun C D)
    (R : Fun D C)
  : Type (max ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂)
  := mk :: (counit : NatTrans (Fun.comp L R) (Fun.id D))
           (unit : NatTrans (Fun.id C) (Fun.comp R L))
           (id_left : ∀ {c : C^.obj}, counit^.com (L^.obj c) ∘∘ L^.hom (unit^.com c) = D^.id (L^.obj c))
           (id_right : ∀ {d : D^.obj}, R^.hom (counit^.com d) ∘∘ unit^.com (R^.obj d) = C^.id (R^.obj d))

-- An adjunction of functors.
-- \dashv
notation L ` ⊣ ` R := Adj L R

/-! #brief The right adjoint of a hom.
-/
definition Adj.right_adj {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {L : Fun C D} {R : Fun D C} (adj : Adj L R)
    {c : C^.obj} {d : D^.obj} (f : D^.hom (L^.obj c) d)
    : C^.hom c (R^.obj d)
:= R^.hom f ∘∘ adj^.unit^.com c

/-! #brief The left adjoint of a hom.
-/
definition Adj.left_adj {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {L : Fun C D} {R : Fun D C} (adj : Adj L R)
    {c : C^.obj} {d : D^.obj} (f : C^.hom c (R^.obj d))
    : D^.hom (L^.obj c) d
:= adj^.counit^.com d ∘∘ L^.hom f

/-! #brief right_adj and left_adj are inverses of one another.
-/
theorem Adj.right_adj_left_adj {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {L : Fun C D} {R : Fun D C} (adj : Adj L R)
    {c : C^.obj} {d : D^.obj} {f : C^.hom c (R^.obj d)}
    : adj^.right_adj (adj^.left_adj f) = f
:= by calc adj^.right_adj (adj^.left_adj f)
               = R^.hom (adj^.counit^.com d ∘∘ L^.hom f) ∘∘ adj^.unit^.com c            : rfl
           ... = R^.hom (adj^.counit^.com d) ∘∘ R^.hom (L^.hom f) ∘∘ adj^.unit^.com c   : by rw R^.hom_circ
           ... = R^.hom (adj^.counit^.com d) ∘∘ (R^.hom (L^.hom f) ∘∘ adj^.unit^.com c) : by rw C^.circ_assoc
           ... = R^.hom (adj^.counit^.com d) ∘∘ ((R □□ L)^.hom f ∘∘ adj^.unit^.com c)   : rfl
           ... = R^.hom (adj^.counit^.com d) ∘∘ (adj^.unit^.com (R^.obj d) ∘∘ f)        : congr_arg (λ q, R^.hom (adj^.counit^.com d) ∘∘ q) (eq.symm (adj^.unit^.natural _))
           ... = R^.hom (adj^.counit^.com d) ∘∘ adj^.unit^.com (R^.obj d) ∘∘ f          : C^.circ_assoc
           ... = ⟨⟨R^.obj d⟩⟩ ∘∘ f                                                      : congr_arg (λ q, q ∘∘ f) adj^.id_right
           ... = f                                                                      : C^.circ_id_left

/-! #brief left_adj and right_adj are inverses of one another.
-/
theorem Adj.left_adj_right_adj {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {L : Fun C D} {R : Fun D C} (adj : Adj L R)
    {c : C^.obj} {d : D^.obj} {f : D^.hom (L^.obj c) d}
    : adj^.left_adj (adj^.right_adj f) = f
:= by calc adj^.left_adj (adj^.right_adj f)
               = adj^.counit^.com d ∘∘ L^.hom (R^.hom f ∘∘ adj^.unit^.com c) : rfl
           ... = adj^.counit^.com d ∘∘ (L^.hom (R^.hom f) ∘∘ L^.hom (adj^.unit^.com c)) : congr_arg (λ q, adj^.counit^.com d ∘∘ q) L^.hom_circ
           ... = adj^.counit^.com d ∘∘ ((L □□ R)^.hom f ∘∘ L^.hom (adj^.unit^.com c))   : rfl
           ... = adj^.counit^.com d ∘∘ (L □□ R)^.hom f ∘∘ L^.hom (adj^.unit^.com c)     : by rw D^.circ_assoc
           ... = f ∘∘ adj^.counit^.com (L^.obj c) ∘∘ L^.hom (adj^.unit^.com c)          : congr_arg (λ q, q ∘∘ L^.hom (adj^.unit^.com c)) (adj^.counit^.natural _)
           ... = f ∘∘ (adj^.counit^.com (L^.obj c) ∘∘ L^.hom (adj^.unit^.com c))        : by rw D^.circ_assoc
           ... = f ∘∘ ⟨⟨L^.obj c⟩⟩                                                      : congr_arg (λ q, f ∘∘ q) adj^.id_left
           ... = f                                                                      : D^.circ_id_right

/-! #brief left_adj is injective.
-/
theorem Adj.left_adj.inj {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {L : Fun C D} {R : Fun D C} (adj : Adj L R)
    {c : C^.obj} {d : D^.obj} {f₁ f₂ : C^.hom c (R^.obj d)}
    (ω : Adj.left_adj adj f₁ = Adj.left_adj adj f₂)
    : f₁ = f₂
:= begin
     apply eq.trans (eq.symm adj^.right_adj_left_adj),
     rw ω,
     apply adj^.right_adj_left_adj
   end

/-! #brief right_adj is injective.
-/
theorem Adj.right_adj.inj {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {L : Fun C D} {R : Fun D C} (adj : Adj L R)
    {c : C^.obj} {d : D^.obj} {f₁ f₂ : D^.hom (L^.obj c) d}
    (ω : Adj.right_adj adj f₁ = Adj.right_adj adj f₂)
    : f₁ = f₂
:= begin
     apply eq.trans (eq.symm adj^.left_adj_right_adj),
     rw ω,
     apply adj^.left_adj_right_adj
   end



/- -----------------------------------------------------------------------
Bijections of categories give adjunctions.
----------------------------------------------------------------------- -/

/-! #brief The adjunction induced by a bijection.
-/
definition Cat.Bij.Adj {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F : Fun C D} {G : Fun D C}
    (FG_Bij : Cat.Bij F G)
    : Adj F G
:= { counit := NatTrans.cast FG_Bij^.id₂
   , unit := NatTrans.cast (eq.symm FG_Bij^.id₁)
   , id_left
      := λ c, begin
                repeat { rw NatTrans.cast.com },
                refine eq.trans (Cat.circ.congr_right Fun.cast_hom) _,
                refine eq.trans cast_hom.circ _,
                apply cast_hom.simp
              end
   , id_right
      := λ c, begin
                repeat { rw NatTrans.cast.com },
                refine eq.trans (Cat.circ.congr_left Fun.cast_hom) _,
                refine eq.trans cast_hom.circ _,
                apply cast_hom.simp
              end
   }

/-! #brief Bijections preserve final objects.
-/
definition Cat.Bij.PresFinal₂ {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F₁ : Fun C D} {F₂ : Fun D C}
    (bij : Cat.Bij F₁ F₂)
    : PresFinal F₂
:= { hom := λ D_HasFinal c, bij^.Adj^.right_adj (@final_hom D D_HasFinal (F₁^.obj c))
   , pres := λ D_HasFinal
             , { hom_uniq := λ c h
                             , begin
                                 apply bij^.Adj^.left_adj.inj,
                                 rw bij^.Adj^.left_adj_right_adj,
                                 apply final_hom.uniq
                               end
               }
   }

/-! #brief Bijections preserve final objects.
-/
definition Cat.Bij.PresFinal₁ {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F₁ : Fun C D} {F₂ : Fun D C}
    (bij : Cat.Bij F₁ F₂)
    : PresFinal F₁
:= bij^.flip^.PresFinal₂

/-! #brief Bijections preserve initial objects.
-/
definition Cat.Bij.PresInit₁ {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F₁ : Fun C D} {F₂ : Fun D C}
    (bij : Cat.Bij F₁ F₂)
    : PresInit F₁
:= { hom := λ C_HasInit c, bij^.Adj^.left_adj (@init_hom _ C_HasInit (F₂^.obj c))
   , pres := λ C_HasInit
             , { hom_uniq := λ c h
                             , begin
                                 apply bij^.Adj^.right_adj.inj,
                                 rw bij^.Adj^.right_adj_left_adj,
                                 apply init_hom.uniq
                               end
               }
   }

/-! #brief Bijections preserve initial objects.
-/
definition Cat.Bij.PresInit₂ {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F₁ : Fun C D} {F₂ : Fun D C}
    (bij : Cat.Bij F₁ F₂)
    : PresInit F₂
:= bij^.flip^.PresInit₁

end qp
