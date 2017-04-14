/- -----------------------------------------------------------------------
Categories.
----------------------------------------------------------------------- -/

import .s1_categories

namespace qp

open stdaux

universe variables ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓobj ℓhom ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂ ℓobj₃ ℓhom₃ ℓobj₄ ℓhom₄ ℓobj₅ ℓhom₅

/-! #brief A functor between categories.
-/
structure Fun (C : Cat.{ℓobj₁ ℓhom₁}) (D : Cat.{ℓobj₂ ℓhom₂})
    : Type (max ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂)
:= (obj : C^.obj → D^.obj)
   (hom : ∀ {x y : C^.obj}, C^.hom x y → D^.hom (obj x) (obj y))
   (hom_id : ∀ {x : C^.obj}, hom ⟨⟨x⟩⟩ = ⟨⟨obj x⟩⟩)
   (hom_circ : ∀ {x y z : C^.obj}
                 {g : C^.hom y z} {f : C^.hom x y}
               , hom (g ∘∘ f) = hom g ∘∘ hom f)

attribute [simp] Fun.hom_id

-- A functor between categories.
-- \rightrightarrows
notation C `⇉` D := Fun C D

/-! #brief Helper for proving two functors are equal.
-/
theorem Fun.eq {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    : ∀ {F G : Fun C D}
        (ωobj : ∀ (x : C^.obj), F^.obj x = G^.obj x)
        (ωhom : ∀ (ω : ∀ (x : C^.obj), F^.obj x = G^.obj x)
                  {x y : C^.obj} (f : C^.hom x y)
                , F^.hom f == G^.hom f)
      , F = G
| (Fun.mk Fobj Fhom Fhom_id Fhom_circ)
  (Fun.mk Gobj Ghom Ghom_id Ghom_circ)
  ωobj ωhom
:= begin
     assert ωobj' : Fobj = Gobj, { exact funext ωobj },
     subst ωobj',
     assert ωhom' : @Fhom = @Ghom,
     { apply funext, intro x,
       apply funext, intro y,
       apply funext, intro f,
       apply eq_of_heq,
       apply ωhom ωobj
     },
     subst ωhom'
   end

/-! #brief Helper for proving two functors are heterogeneously equal.
-/
theorem Fun.heq
    : ∀ {C₁ : Cat.{ℓobj₁ ℓhom₁}} {D₁ : Cat.{ℓobj₂ ℓhom₂}} {F₁ : Fun C₁ D₁}
        {C₂ : Cat.{ℓobj₁ ℓhom₁}} {D₂ : Cat.{ℓobj₂ ℓhom₂}} {F₂ : Fun C₂ D₂}
        (ωC : C₁ = C₂) (ωD : D₁ = D₂)
        (ωobj : ∀ (x₁ : C₁^.obj) (x₂ : C₂^.obj)
                , x₁ == x₂ → F₁^.obj x₁ == F₂^.obj x₂)
        (ωhom : ∀ (x₁ y₁ : C₁^.obj) (x₂ y₂ : C₂^.obj)
                  (f₁ : C₁^.hom x₁ y₁) (f₂ : C₂^.hom x₂ y₂)
                , f₁ == f₂ → (F₁^.hom f₁) == (F₂^.hom f₂))
      , F₁ == F₂
| C D F₁ .(C) .(D) F₂ (eq.refl .(C)) (eq.refl .(D)) ωobj ωhom
:= begin
     apply heq_of_eq,
     apply Fun.eq,
     { intro x,
       apply eq_of_heq,
       apply ωobj,
       apply heq.refl
     },
     { intros ωobj x y f,
       apply ωhom,
       apply heq.refl
     }
   end

/-! #brief Congruence on objects.
-/
theorem Fun.congr_obj {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F : Fun C D}
    : ∀ {x y : C^.obj}
        (ω : x = y)
      , F^.obj x = F^.obj y
| x .(x) (eq.refl .(x)) := rfl

/-! #brief Congruence on homs.
-/
theorem Fun.congr_hom {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F : Fun C D}
    : ∀ {x y : C^.obj} {f₁ f₂ : C^.hom x y}
        (ω : f₁ = f₂)
      , F^.hom f₁ = F^.hom f₂
| x y f .(f) (eq.refl .(f)) := rfl

/-! #brief Action of a functor on a cast_hom.
-/
theorem Fun.cast_hom {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F : Fun C D}
    : ∀ {x y : C^.obj}
        {ω : x = y}
      , F^.hom (cast_hom ω) = cast_hom begin rw ω end
| x .(x) (eq.refl .(x)) := F^.hom_id



/- -----------------------------------------------------------------------
Functors are morphisms of categories.
----------------------------------------------------------------------- -/

/-! #brief The identity functor.
-/
definition Fun.id (C : Cat.{ℓobj ℓhom}) : Fun C C
:= { obj := λ x, x
   , hom := λ x y f, f
   , hom_id := λ x, rfl
   , hom_circ := λ x y z g f, rfl
   }

@[simp] theorem Fun.id.simp_obj {C : Cat.{ℓobj ℓhom}}
    (c : C^.obj)
    : (Fun.id C)^.obj c = c
:= rfl

@[simp] theorem Fun.id.simp_hom {C : Cat.{ℓobj ℓhom}}
    {c₁ c₂ : C^.obj} (f : C^.hom c₁ c₂)
    : (Fun.id C)^.hom f = f
:= rfl

/-! #brief Composition of functors.
-/
definition Fun.comp {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    (G : Fun C D) (F : Fun B C)
    : Fun B D
:= { obj := λ x, G^.obj (F^.obj x)
   , hom := λ x y f, G^.hom (F^.hom f)
   , hom_id := λ x, begin dsimp, simp end
   , hom_circ := λ x y z g f, begin dsimp, simp [Fun.hom_circ] end
   }

-- Composition of functors.
-- \Box\Box
infixl ` □□ ` : 150 := Fun.comp

@[simp] theorem Fun.comp.simp_obj {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    (G : Fun C D) (F : Fun B C) (x : B^.obj)
    : (Fun.comp G F)^.obj x = G^.obj (F^.obj x)
:= rfl

@[simp] theorem Fun.comp.simp_hom {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    (G : Fun C D) (F : Fun B C) {x₁ x₂ : B^.obj} (f : B^.hom x₁ x₂)
    : (Fun.comp G F)^.hom f = G^.hom (F^.hom f)
:= rfl

/-! #brief Composition of functors is associative.
-/
theorem Fun.comp_assoc {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}} {E : Cat.{ℓobj₄ ℓhom₄}}
    {H : Fun D E} {G : Fun C D} {F : Fun B C}
    : Fun.comp H (Fun.comp G F) = Fun.comp (Fun.comp H G) F
:= begin
     apply Fun.eq,
     { intro b, repeat {rw [Fun.comp.simp_obj]} },
     { intros ωobj x y f, repeat {rw [Fun.comp.simp_hom]}, apply heq.refl }
   end

/-! #brief The identity functor is a left-identity for composition.
-/
@[simp] theorem Fun.comp_id_left {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F : Fun C D}
    : Fun.comp (Fun.id D) F = F
:= begin
     apply Fun.eq,
     { intro x, rw [Fun.comp.simp_obj, Fun.id.simp_obj] },
     { intros ωobj x y f, rw [Fun.comp.simp_hom, Fun.id.simp_hom], apply heq.refl }
   end

/-! #brief The identity functor is a right-identity for composition.
-/
@[simp] theorem Fun.comp_id_right {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F : Fun C D}
    : Fun.comp F (Fun.id C) = F
:= begin
     apply Fun.eq,
     { intro x, rw [Fun.comp.simp_obj, Fun.id.simp_obj] },
     { intros ωobj x y f, rw [Fun.comp.simp_hom, Fun.id.simp_hom], apply heq.refl }
   end

/-! #brief Iterated composition of endofunctors.
-/
definition Fun.iter_comp {C : Cat.{ℓobj₁ ℓhom₁}}
    (F : Fun C C)
    : ℕ → Fun C C
| 0 := Fun.id C
| (nat.succ n) := Fun.comp F (Fun.iter_comp n)

/-! #brief Fun.iter_comp absorbs on the left.
-/
definition Fun.iter_comp_fold_left {C : Cat.{ℓobj₁ ℓhom₁}}
    {F : Fun C C}
    {n : ℕ}
    : Fun.comp F (Fun.iter_comp F n)
       = Fun.iter_comp F (nat.succ n)
:= rfl

/-! #brief Fun.iter_comp absorbs on the right.
-/
definition Fun.iter_comp_fold_right {C : Cat.{ℓobj₁ ℓhom₁}}
    {F : Fun C C}
    : ∀ {n : ℕ}
      , Fun.comp (Fun.iter_comp F n) F
         = Fun.iter_comp F (nat.succ n)
| 0 := rfl
| (nat.succ n)
:= begin
     dsimp [Fun.iter_comp],
     rw -Fun.comp_assoc,
     rw Fun.iter_comp_fold_right,
     trivial
   end

/-! #brief Iterated composition of endofunctors.
-/
definition Fun.iter_comp' {C : Cat.{ℓobj₁ ℓhom₁}}
    (F : Fun C C)
    : ℕ → Fun C C
| 0 := Fun.id C
| (nat.succ n) := Fun.comp (Fun.iter_comp' n) F

/-! @brief Fun.iter_comp and Fun.iter_comp' are equal.
-/
theorem Fun.iter_comp_assoc {C : Cat.{ℓobj₁ ℓhom₁}}
    {F : Fun C C}
    : ∀ {n : ℕ}
      , Fun.iter_comp F n = Fun.iter_comp' F n
| 0 := rfl
| (nat.succ n)
:= begin
     dsimp [Fun.iter_comp, Fun.iter_comp'],
     rw [-Fun.iter_comp_assoc, Fun.iter_comp_fold_left, Fun.iter_comp_fold_right]
   end

/-! #brief Fun.iter_comp absorbs on the left.
-/
definition Fun.iter_comp'_fold_left {C : Cat.{ℓobj₁ ℓhom₁}}
    {F : Fun C C}
    {n : ℕ}
    : Fun.comp F (Fun.iter_comp' F n)
       = Fun.iter_comp' F (nat.succ n)
:= begin
     repeat { rw -Fun.iter_comp_assoc },
     exact Fun.iter_comp_fold_left
   end

/-! #brief Fun.iter_comp absorbs on the right.
-/
definition Fun.iter_comp'_fold_right {C : Cat.{ℓobj₁ ℓhom₁}}
    {F : Fun C C}
    {n : ℕ}
    : Fun.comp (Fun.iter_comp' F n) F
       = Fun.iter_comp' F (nat.succ n)
:= begin
     repeat { rw -Fun.iter_comp_assoc },
     exact Fun.iter_comp_fold_right
   end



/- -----------------------------------------------------------------------
Constant functors.
----------------------------------------------------------------------- -/

/-! #brief A constant functor.
-/
definition ConstFun (C : Cat.{ℓobj₁ ℓhom₁}) {D : Cat.{ℓobj₂ ℓhom₂}}
    (d : D^.obj)
    : Fun C D
:= { obj := λ c, d
   , hom := λ c₁ c₂ f, D^.id d
   , hom_id := λ c, rfl
   , hom_circ := λ c₁ c₂ c₃ g f, eq.symm D^.circ_id_right
   }



/- -----------------------------------------------------------------------
The initial and final functors.
----------------------------------------------------------------------- -/

/-! #brief The final functor.
-/
definition FinalFun (C : Cat.{ℓobj₂ ℓhom₂})
    : Fun C UnitCat.{ℓobj₁ ℓhom₁}
:= { obj := λ c, punit.star
   , hom := λ c₁ c₂ f, punit.star
   , hom_id := λ c, rfl
   , hom_circ := λ c₁ c₂ c₃ g f, rfl
   }

/-! #brief The final functor is unique.
-/
theorem FinalFun.uniq {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : Fun C UnitCat.{ℓobj₁ ℓhom₁}}
    : F = FinalFun.{ℓobj₁ ℓhom₁} C
:= Fun.eq
    (λ c, begin cases F^.obj c, trivial end)
    (λ ω c₁ c₂ f, begin cases F^.hom f, trivial end)

/-! #brief The initial functor.
-/
definition InitFun (C : Cat.{ℓobj₂ ℓhom₂})
    : Fun EmptyCat.{ℓobj₁ ℓhom₁} C
:= { obj := λ e, by cases e
   , hom := λ e₁ e₂ f, by cases f
   , hom_id := λ e, by cases e
   , hom_circ := λ e₁ e₂ e₃ g f, by cases f
   }

/-! #brief The initial functor is unique.
-/
theorem InitFun.uniq {C : Cat.{ℓobj₂ ℓhom₂}}
    {F : Fun EmptyCat.{ℓobj₁ ℓhom₁} C}
    : F = InitFun.{ℓobj₁ ℓhom₁} C
:= Fun.eq
    (λ c, by cases c)
    (λ ω c₁ c₂ f, by cases f)



/- -----------------------------------------------------------------------
Functors and isomorphisms.
----------------------------------------------------------------------- -/

/-! #brief Functors preserve isomorphisms.
-/
theorem Fun.preserves_Iso {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    (F : Fun C D)
    {c₁ c₂ : C^.obj}
    {f₁₂ : C^.hom c₁ c₂} {f₂₁ : C^.hom c₂ c₁}
    (iso : Iso f₁₂ f₂₁)
    : Iso (F^.hom f₁₂) (F^.hom f₂₁)
:= { id₁ := by calc F^.hom f₂₁ ∘∘ F^.hom f₁₂
                        = F^.hom (f₂₁ ∘∘ f₁₂) : by rw F^.hom_circ
                    ... = F^.hom (C^.id c₁)   : by rw iso^.id₁
                    ... = ⟨⟨F^.obj c₁⟩⟩       : by rw F^.hom_id
   , id₂ := by calc F^.hom f₁₂ ∘∘ F^.hom f₂₁
                        = F^.hom (f₁₂ ∘∘ f₂₁) : by rw F^.hom_circ
                    ... = F^.hom (C^.id c₂)   : by rw iso^.id₂
                    ... = ⟨⟨F^.obj c₂⟩⟩       : by rw F^.hom_id
   }



/- -----------------------------------------------------------------------
The category of categories.
----------------------------------------------------------------------- -/

/-! #brief A category of categories.
-/
definition CatOfCats
    : Cat.{((max ℓobj ℓhom) + 1) ((max ℓobj ℓhom) + 1)}
:= { obj := Cat.{ℓobj ℓhom}
   , hom := Fun
   , id := Fun.id
   , circ := @Fun.comp
   , circ_assoc := @Fun.comp_assoc
   , circ_id_left := @Fun.comp_id_left
   , circ_id_right := @Fun.comp_id_right
   }

/-! #brief The Lean object functor.
-/
definition CatOfCats.ObjFun
    : Fun CatOfCats.{ℓobj ℓhom} LeanCat.{ℓobj}
:= { obj := λ C, C^.obj
   , hom := λ C₁ C₂ F, F^.obj
   , hom_id := λ C, rfl
   , hom_circ := λ C₁ C₂ C₃ g f, rfl
   }

/-! #brief A general hom in a category.
-/
structure Cat.GeneralHom (C : Cat.{ℓobj₁ ℓhom₁})
    : Type (max ℓobj₁ ℓhom₁)
:= (dom : C^.obj)
   (codom : C^.obj)
   (hom : C^.hom dom codom)

/-! #brief The Lean hom functor.
-/
definition CatOfCats.HomFun
    : Fun CatOfCats.{ℓobj ℓhom} LeanCat.{max ℓobj ℓhom}
:= { obj := Cat.GeneralHom
   , hom
      := λ C₁ C₂ F h
         , { dom := F^.obj h^.dom
           , codom := F^.obj h^.codom
           , hom := F^.hom h^.hom
           }
   , hom_id := λ C, begin apply funext, intro x, cases x, trivial end
   , hom_circ := λ C₁ C₂ C₃ g f, begin apply funext, intro x, cases x, trivial end
   }



/- -----------------------------------------------------------------------
The Lean universe-level functors.
----------------------------------------------------------------------- -/

/-! #brief Lift the universe level to the max.
-/
inductive Lean.LevelMax (A : Type.{ℓ₁}) : Type (max ℓ₁ ℓ₂)
| lift : A → Lean.LevelMax

definition Lean.LevelMax.unlift {A : Type.{ℓ₁}}
    : Lean.LevelMax.{ℓ₁ ℓ₂} A → A
| (Lean.LevelMax.lift a) := a

-- /-! #brief Lean.LevelMax.lift is injective.
-- -/
-- theorem Lean.LevelMax.lift.inj {A : Type.{ℓ₁}}
--     : ∀ {a₁ a₂ : A}
--         (ω : Lean.LevelMax.lift.{ℓ₁ ℓ₂} a₁ = Lean.LevelMax.lift.{ℓ₁ ℓ₂} a₂)
--       , a₁ = a₂
-- | a .(a) (eq.refl .(Lean.LevelMax.lift.{ℓ₁ ℓ₂} a)) := rfl

/-! #brief Apply a function to a Lean.Level1.
-/
definition Lean.LevelMax.map {A : Type.{ℓ₁}} {B : Type.{ℓ₂}}
    (f : A → B)
    : Lean.LevelMax.{ℓ₁ ℓ₃} A → Lean.LevelMax.{ℓ₂ ℓ₄} B
| (Lean.LevelMax.lift a) := Lean.LevelMax.lift (f a)

/-! #brief Increasing the universe level to the max.
-/
definition LeanCat.LevelMax
    : Fun LeanCat.{ℓ₁} LeanCat.{max ℓ₁ ℓ₂}
:= { obj := Lean.LevelMax
   , hom := @Lean.LevelMax.map
   , hom_id := λ X, begin apply funext, intro x, cases x, trivial end
   , hom_circ := λ X Y Z g f, begin apply funext, intro x, cases x, trivial end
   }

/-! #brief Lift the universe level of a type by 1.
-/
@[reducible] definition Lean.Level1 (A : Type.{ℓ₁}) : Type (ℓ₁ + 1)
:= Lean.LevelMax.{ℓ₁ (ℓ₁ + 1)} A

/-! #brief Apply a function to a Lean.Level1.
-/
definition Lean.Level1.map {A : Type.{ℓ₁}} {B : Type.{ℓ₂}}
    (f : A → B)
    : Lean.Level1 A → Lean.Level1 B
:= Lean.LevelMax.map f

/-! #brief Increasing the universe level by 1.
-/
definition LeanCat.Level1
    : Fun LeanCat.{ℓ₁} LeanCat.{ℓ₁ + 1}
:= LeanCat.LevelMax.{ℓ₁ (ℓ₁ + 1)}

/- -----------------------------------------------------------------------
Bijections of categories and conjugate functors.
----------------------------------------------------------------------- -/

/-! #brief A bijection of categories.
-/
structure Cat.Bij {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    (F : Fun C D)
    (G : Fun D C)
    : Prop
:= (id₁ : Fun.comp G F = Fun.id C)
   (id₂ : Fun.comp F G = Fun.id D)

/-! #brief Bijections of categories can be 'flipped' to the other direction.
-/
theorem Cat.Bij.flip {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F : Fun C D}
    {G : Fun D C}
    (bij : Cat.Bij F G)
    : Cat.Bij G F
:= { id₁ := bij^.id₂
   , id₂ := bij^.id₁
   }

/-! #brief Bijections have unique inverses.
-/
theorem Cat.Bij.inv_uniq₂ {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F : Fun C D}
    {G₁ G₂ : Fun D C}
    (bij₁ : Cat.Bij F G₁)
    (bij₂ : Cat.Bij F G₂)
    : G₁ = G₂
:= by calc G₁  = G₁ □□ Fun.id D : by rw Fun.comp_id_right
           ... = G₁ □□ (F □□ G₂) : by rw bij₂^.id₂
           ... = G₁ □□ F □□ G₂   : by rw Fun.comp_assoc
           ... = Fun.id C □□ G₂ : by rw bij₁^.id₁
           ... = G₂             : by rw Fun.comp_id_left

/-! #brief Bijections have unique inverses.
-/
theorem Cat.Bij.inv_uniq₁ {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F₁ F₂ : Fun C D}
    {G : Fun D C}
    (bij₁ : Cat.Bij F₁ G)
    (bij₂ : Cat.Bij F₂ G)
    : F₁ = F₂
:= Cat.Bij.inv_uniq₂ (Cat.Bij.flip bij₁) (Cat.Bij.flip bij₂)

/-! #brief The identity functor is a bijection of categories.
-/
theorem Fun.id.Bij (C : Cat.{ℓobj ℓhom})
    : Cat.Bij (Fun.id C) (Fun.id C)
:= { id₁ := Fun.comp_id_left
   , id₂ := Fun.comp_id_left
   }

/-! #brief The composition of two bijections is again a bijection.
-/
theorem Fun.comp.bij
    {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    {F₂ : Fun C D} {G₂ : Fun D C} (bij₂ : Cat.Bij F₂ G₂)
    {F₁ : Fun B C} {G₁ : Fun C B} (bij₁ : Cat.Bij F₁ G₁)
    : Cat.Bij (Fun.comp F₂ F₁) (Fun.comp G₁ G₂)
:= { id₁
      := by calc
          G₁ □□ G₂ □□ (F₂ □□ F₁)
              = G₁ □□ (G₂ □□ F₂) □□ F₁  : by repeat { rw Fun.comp_assoc }
          ... = G₁ □□ Fun.id C □□ F₁    : by rw bij₂^.id₁
          ... = G₁ □□ F₁                : by rw Fun.comp_id_right
          ... = Fun.id B                : by rw bij₁^.id₁
   , id₂
      := by calc
          F₂ □□ F₁ □□ (G₁ □□ G₂)
              = F₂ □□ (F₁ □□ G₁) □□ G₂  : by repeat { rw Fun.comp_assoc }
          ... = F₂ □□ (Fun.id C) □□ G₂  : by rw bij₁^.id₂
          ... = F₂ □□ G₂                : by rw Fun.comp_id_right
          ... = Fun.id D                : by rw bij₂^.id₂
   }

/-! #brief The casting functor.
-/
definition CastFun
    : ∀ {C₁ C₂ : Cat.{ℓobj ℓhom}}
        (ω : C₁ = C₂)
       , Fun C₁ C₂
| C .(C) (eq.refl .(C)) := Fun.id C

/-! #brief The casting functor is trivial on eq.refl.
-/
theorem CastFun.refl
    : ∀ {C : Cat.{ℓobj ℓhom}}
         (ω : C = C)
      , CastFun ω = Fun.id C
| C (eq.refl .(C)) := rfl

/-! #brief The casting functor is compatible with transitivity.
-/
theorem CastFun.trans
    : ∀ {C₁ C₂ C₃ : Cat.{ℓobj ℓhom}}
        (ω₂₃ : C₂ = C₃)
        (ω₁₂ : C₁ = C₂)
      , CastFun ω₂₃ □□ CastFun ω₁₂ = CastFun (eq.trans ω₁₂ ω₂₃)
| C .(C) .(C) (eq.refl .(C)) (eq.refl .(C)) := Fun.comp_id_right

/-! #brief The casting functor is a bijection of categories.
-/
theorem CastFun.Bij
    : ∀ {C₁ C₂ : Cat.{ℓobj ℓhom}}
         (ω₁₂ : C₁ = C₂)
         (ω₂₁ : C₂ = C₁)
      , Cat.Bij (CastFun ω₁₂) (CastFun ω₂₁)
| C .(C) (eq.refl .(C)) (eq.refl .(C)) := Fun.id.Bij C

/-! #brief A pair of conjugate functors.
-/
structure Fun.Conj {C₁ C₂ : Cat.{ℓobj₁ ℓhom₁}} {D₁ D₂ : Cat.{ℓobj₂ ℓhom₂}}
    (FC₁₂ : Fun C₁ C₂) (FC₂₁ : Fun C₂ C₁)
    (FD₁₂ : Fun D₁ D₂) (FD₂₁ : Fun D₂ D₁)
    (F₁ : Fun C₁ D₁) (F₂ : Fun C₂ D₂)
    : Prop
:= (dom_bij : Cat.Bij FC₁₂ FC₂₁)
   (codom_bij : Cat.Bij FD₁₂ FD₂₁)
   (id₂ : F₂ = Fun.comp (Fun.comp FD₁₂ F₁) FC₂₁)

theorem Fun.Conj.outside {C₁ C₂ : Cat.{ℓobj₁ ℓhom₁}} {D₁ D₂ : Cat.{ℓobj₂ ℓhom₂}}
    {FC₁₂ : Fun C₁ C₂} {FC₂₁ : Fun C₂ C₁}
    {FD₁₂ : Fun D₁ D₂} {FD₂₁ : Fun D₂ D₁}
    {F₁ : Fun C₁ D₁} {F₂ : Fun C₂ D₂}
    (conj : Fun.Conj FC₁₂ FC₂₁ FD₁₂ FD₂₁ F₁ F₂)
    : Fun.comp FD₂₁ F₂ = Fun.comp F₁ FC₂₁
:= by calc FD₂₁ □□ F₂
               = FD₂₁ □□ (FD₁₂ □□ F₁ □□ FC₂₁) : by rw conj^.id₂
           ... = (FD₂₁ □□ FD₁₂) □□ F₁ □□ FC₂₁ : by repeat {rw Fun.comp_assoc}
           ... = Fun.id D₁ □□ F₁ □□ FC₂₁     : by rw conj^.codom_bij^.id₁
           ... = F₁ □□ FC₂₁                   : by rw Fun.comp_id_left

theorem Fun.Conj.inside {C₁ C₂ : Cat.{ℓobj₁ ℓhom₁}} {D₁ D₂ : Cat.{ℓobj₂ ℓhom₂}}
    {FC₁₂ : Fun C₁ C₂} {FC₂₁ : Fun C₂ C₁}
    {FD₁₂ : Fun D₁ D₂} {FD₂₁ : Fun D₂ D₁}
    {F₁ : Fun C₁ D₁} {F₂ : Fun C₂ D₂}
    (conj : Fun.Conj FC₁₂ FC₂₁ FD₁₂ FD₂₁ F₁ F₂)
    : Fun.comp F₂ FC₁₂ = Fun.comp FD₁₂ F₁
:= by calc F₂ □□ FC₁₂
               = (FD₁₂ □□ F₁ □□ FC₂₁) □□ FC₁₂ : by rw conj^.id₂
           ... = FD₁₂ □□ F₁ □□ (FC₂₁ □□ FC₁₂) : by repeat {rw Fun.comp_assoc}
           ... = FD₁₂ □□ F₁ □□ Fun.id C₁     : by rw conj^.dom_bij^.id₁
           ... = FD₁₂ □□ F₁                  : by rw Fun.comp_id_right

theorem Fun.Conj.id₁ {C₁ C₂ : Cat.{ℓobj₁ ℓhom₁}} {D₁ D₂ : Cat.{ℓobj₂ ℓhom₂}}
    {FC₁₂ : Fun C₁ C₂} {FC₂₁ : Fun C₂ C₁}
    {FD₁₂ : Fun D₁ D₂} {FD₂₁ : Fun D₂ D₁}
    {F₁ : Fun C₁ D₁} {F₂ : Fun C₂ D₂}
    (conj : Fun.Conj FC₁₂ FC₂₁ FD₁₂ FD₂₁ F₁ F₂)
    : Fun.comp (Fun.comp FD₂₁ F₂) FC₁₂ = F₁
:= by calc FD₂₁ □□ F₂ □□ FC₁₂
               = FD₂₁ □□ (FD₁₂ □□ F₁ □□ FC₂₁) □□ FC₁₂   : by rw conj^.id₂
           ... = (FD₂₁ □□ FD₁₂) □□ F₁ □□ (FC₂₁ □□ FC₁₂) : by repeat {rw Fun.comp_assoc}
           ... = Fun.id D₁ □□ F₁ □□ Fun.id C₁           : by rw [conj^.dom_bij^.id₁, conj^.codom_bij^.id₁]
           ... = F₁                                     : by rw [Fun.comp_id_left, Fun.comp_id_right]

/-! #brief Conjugate functors can be 'flipped' to the other direction.
-/
theorem Fun.conj {C₁ C₂ : Cat.{ℓobj₁ ℓhom₁}} {D₁ D₂ : Cat.{ℓobj₂ ℓhom₂}}
    {FC₁₂ : Fun C₁ C₂} {FC₂₁ : Fun C₂ C₁}
    {FD₁₂ : Fun D₁ D₂} {FD₂₁ : Fun D₂ D₁}
    {F₁ : Fun C₁ D₁} {F₂ : Fun C₂ D₂}
    (conj : Fun.Conj FC₁₂ FC₂₁ FD₁₂ FD₂₁ F₁ F₂)
    : Fun.Conj FC₂₁ FC₁₂ FD₂₁ FD₁₂ F₂ F₁
:= { dom_bij := Cat.Bij.flip conj^.dom_bij
   , codom_bij := Cat.Bij.flip conj^.codom_bij
   , id₂ := eq.symm conj^.id₁
   }



/- -----------------------------------------------------------------------
Over-categories over final objects.
----------------------------------------------------------------------- -/

/-! #brief The over-category over a final is iso to the original category.
-/
definition OverFinal.to (C : Cat.{ℓobj ℓhom})
    [C_HasFinal : HasFinal C]
    : Fun C (OverCat C (final C))
:= { obj := λ c, { obj := c, hom := final_hom c }
   , hom := λ c₁ c₂ f, { hom := f, triangle := eq.symm (final_hom.uniq C) }
   , hom_id := λ c, OverHom.eq rfl
   , hom_circ := λ c₁ c₂ c₃ g f, OverHom.eq rfl
   }

/-! #brief The over-category over a final is iso to the original category.
-/
definition OverFinal.from (C : Cat.{ℓobj ℓhom})
    [C_HasFinal : HasFinal C]
    : Fun (OverCat C (final C)) C
:= { obj := λ c, c^.obj
   , hom := λ c₁ c₂ f, f^.hom
   , hom_id := λ c, rfl
   , hom_circ := λ c₁ c₂ c₃ g f, rfl
   }

/-! #brief The over-category over a final is iso to the original category.
-/
definition OverFinal.Bij (C : Cat.{ℓobj ℓhom})
    [C_HasFinal : HasFinal C]
    : Cat.Bij (OverFinal.to C) (OverFinal.from C)
:= { id₁ := rfl
   , id₂ := Fun.eq
             (λ c, OverObj.eq rfl (heq_of_eq (eq.symm (final_hom.uniq C))))
             (λ ω x y f, OverHom.heq (ω _) (ω _) (heq.refl _))
   }


/- -----------------------------------------------------------------------
Forgetful functors between the algebraic categories.
----------------------------------------------------------------------- -/

/-! #brief The forgetful functor from CatOfMonoids to CatOfSemigroups.
-/
definition FrgtMonoidSemigroupFun
    : Fun CatOfMonoids.{ℓ₁} CatOfSemigroups.{ℓ₁}
:= { obj := λ A
            , { fst := A^.fst
              , snd := @monoid.to_semigroup A^.fst A^.snd
              }
   , hom := λ A B f
            , { val := f^.val
              , property := monoid.hom.to_hom f^.property
              }
   , hom_id := λ A, subtype.eq rfl
   , hom_circ := λ A B C g f, subtype.eq rfl
   }

/-! #brief The forgetful functor from CatOfGroups to CatOfMonoids.
-/
definition FrgtGroupMonoidFun
    : Fun CatOfGroups.{ℓ₁} CatOfMonoids.{ℓ₁}
:= { obj := λ A
            , { fst := A^.fst
              , snd := @group.to_monoid A^.fst A^.snd
              }
   , hom := λ A B f
            , { val := f^.val
              , property := @group.hom.to_monoid_hom _ A^.snd _ B^.snd _ f^.property
              }
   , hom_id := λ A, subtype.eq rfl
   , hom_circ := λ A B C g f, subtype.eq rfl
   }



/- -----------------------------------------------------------------------
Functors between categories induced by monoids and groups.
----------------------------------------------------------------------- -/

/-! #brief Every monoid homomorphism induces a functor.
-/
definition MonoidFun
    {A : Type ℓ₁} [A_monoid : monoid A]
    {B : Type ℓ₁} [B_monoid : monoid B]
    {f : A → B}
    (f_hom : monoid.hom f)
    : Fun (MonoidCat A) (MonoidCat B)
:= { obj := λ u, punit.star
   , hom := λ u₁ u₂ a, f a
   , hom_id := λ u, f_hom^.id
   , hom_circ := λ u₁ u₂ u₃ a₂ a₁, f_hom^.dist a₂ a₁
   }

/-! #brief Every group homomorphism induces a functor.
-/
definition GroupFun
    {A : Type ℓ₁} [A_group : group A]
    {B : Type ℓ₁} [B_group : group B]
    {f : A → B}
    (f_hom : group.hom f)
    : Fun (GroupCat A) (GroupCat B)
:= MonoidFun (group.hom.to_monoid_hom f_hom)



/- -----------------------------------------------------------------------
Functors between preorder categories.
----------------------------------------------------------------------- -/

/-! #brief Every monotone function induces a functor.
-/
definition PreorderFun
    {A : Type ℓ₁} {r : A → A → Prop}
    {r_refl : reflexive r} {r_trans : transitive r}
    {B : Type ℓ₂} {s : B → B → Prop}
    {s_refl : reflexive s} {s_trans : transitive s}
    (f : A → B)
    (f_monotone : monotone r s f)
    : Fun (PreorderCat r r_refl r_trans) (PreorderCat s s_refl s_trans)
:= { obj := f
   , hom := f_monotone
   , hom_id := λ a, proof_irrel _ _
   , hom_circ := λ a₁ a₂ a₃ g f, proof_irrel _ _
   }

@[simp] definition PreorderFun.simp_obj
    {A : Type ℓ₁} {r : A → A → Prop}
    {r_refl : reflexive r} {r_trans : transitive r}
    {B : Type ℓ₂} {s : B → B → Prop}
    {s_refl : reflexive s} {s_trans : transitive s}
    (f : A → B)
    (f_monotone : monotone r s f)
    (a : A)
    : (@PreorderFun A r r_refl r_trans B s s_refl s_trans f f_monotone)^.obj a = f a
:= rfl

@[simp] definition PreorderFun.simp_hom
    {A : Type ℓ₁} {r : A → A → Prop}
    {r_refl : reflexive r} {r_trans : transitive r}
    {B : Type ℓ₂} {s : B → B → Prop}
    {s_refl : reflexive s} {s_trans : transitive s}
    (f : A → B)
    (f_monotone : monotone r s f)
    {a₁ a₂ : A} (ω : r a₁ a₂)
    : (@PreorderFun A r r_refl r_trans B s s_refl s_trans f f_monotone)^.hom ω = f_monotone a₁ a₂ ω
:= rfl

/-! #brief Every function induces a functor between object categories.
-/
definition ObjFun {A : Type ℓ₁} {B : Type ℓ₂} (f : A → B)
    : Fun (ObjCat A) (ObjCat B)
:= PreorderFun f (λ a₁ a₂, congr_arg f)

@[simp] definition ObjFun.simp_obj {A : Type ℓ₁} {B : Type ℓ₂} (f : A → B)
    (a : A)
    : (ObjFun f)^.obj a = f a
:= rfl

@[simp] definition ObjFun.simp_hom {A : Type ℓ₁} {B : Type ℓ₂} (f : A → B)
    {a₁ a₂ : A} (ω : a₁ = a₂)
    : (ObjFun f)^.hom ω = congr_arg f ω
:= rfl



/- -----------------------------------------------------------------------
Functors out of product categories.
----------------------------------------------------------------------- -/

/-! #brief Left-projection out of a product category.
-/
definition ProdCat.π₁ (C : Cat.{ℓobj₁ ℓhom₁}) (D : Cat.{ℓobj₂ ℓhom₂})
    : Fun (ProdCat C D) C
:= { obj := λ x, x^.fst
   , hom := λ x y f, f^.fst
   , hom_id := λ x, rfl
   , hom_circ := λ x y z g f, rfl
   }

/-! #brief Right-projection out of a product category.
-/
definition ProdCat.π₂ (C : Cat.{ℓobj₁ ℓhom₁}) (D : Cat.{ℓobj₂ ℓhom₂})
    : Fun (ProdCat C D) D
:= { obj := λ x, x^.snd
   , hom := λ x y f, f^.snd
   , hom_id := λ x, rfl
   , hom_circ := λ x y z g f, rfl
   }

/-! #brief Pairs of functors induce functors into the product category.
-/
definition ProdCat.into {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    (l : Fun B C)
    (r : Fun B D)
    : Fun B (ProdCat C D)
:= { obj := λ b, { fst := l^.obj b, snd := r^.obj b }
   , hom := λ b₁ b₂ f, { fst := l^.hom f, snd := r^.hom f }
   , hom_id := λ b, begin rw [l^.hom_id, r^.hom_id], trivial end
   , hom_circ := λ b₁ b₂ b₃ g f, begin rw [l^.hom_circ, r^.hom_circ], trivial end
   }

/-! #brief Factoring through Product.into.
-/
theorem ProdCat.π₁_into {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    {l : Fun B C}
    {r : Fun B D}
    : Fun.comp (ProdCat.π₁ C D) (ProdCat.into l r) = l
:= begin
     apply Fun.eq,
     { intro b, trivial },
     { intros ωobj b₁ b₂ f, trivial },
   end

/-! #brief Factoring through Product.into.
-/
theorem ProdCat.π₂_into {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    {l : Fun B C}
    {r : Fun B D}
    : Fun.comp (ProdCat.π₂ C D) (ProdCat.into l r) = r
:= begin
     apply Fun.eq,
     { intro b, trivial },
     { intros ωobj b₁ b₂ f, trivial },
   end

/-! #brief ProdCat.into on the projections is trivial.
-/
theorem ProdCat.into_π {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    : ProdCat.into (ProdCat.π₁ C D) (ProdCat.π₂ C D) = Fun.id (ProdCat C D)
:= begin
     apply Fun.eq,
     { intro cd, cases cd with c d, trivial },
     { intros ωobj cd₁ cd₂ f, cases f with f₁ f₂, trivial }
   end

/-! #brief Composition of ProdCat.into.
-/
theorem ProdCat.into.comp
    {A : Cat.{ℓobj₁ ℓhom₁}}
    {B : Cat.{ℓobj₂ ℓhom₂}}
    {C : Cat.{ℓobj₃ ℓhom₃}}
    {D : Cat.{ℓobj₄ ℓhom₄}}
    {E : Cat.{ℓobj₅ ℓhom₅}}
    {l₁ : Fun A B} {r₁ : Fun A C}
    {l₂ : Fun (ProdCat B C) D} {r₂ : Fun (ProdCat B C) E}
    : Fun.comp (ProdCat.into l₂ r₂) (ProdCat.into l₁ r₁)
       = ProdCat.into (Fun.comp l₂ (ProdCat.into l₁ r₁))
                      (Fun.comp r₂ (ProdCat.into l₁ r₁))
:= begin
     apply Fun.eq,
     { intro a, trivial },
     { intros ωobj a₁ a₂ f, trivial },
   end

/-! #brief Flipping the order of a product.
-/
definition ProdCat.flip (C : Cat.{ℓobj₁ ℓhom₁}) (D : Cat.{ℓobj₂ ℓhom₂})
    : Fun (ProdCat C D) (ProdCat D C)
:= ProdCat.into (ProdCat.π₂ C D) (ProdCat.π₁ C D)

/-! #brief Flipping the order of a product is a bijection of categories.
-/
theorem ProdCat.flip.Bij (C : Cat.{ℓobj₁ ℓhom₁}) (D : Cat.{ℓobj₂ ℓhom₂})
    : Cat.Bij (ProdCat.flip C D) (ProdCat.flip D C)
:= { id₁ := begin
              unfold ProdCat.flip,
              rw [ProdCat.into.comp, ProdCat.π₂_into, ProdCat.π₁_into, ProdCat.into_π]
            end
   , id₂ := begin
              unfold ProdCat.flip,
              rw [ProdCat.into.comp, ProdCat.π₂_into, ProdCat.π₁_into, ProdCat.into_π]
            end
   }



/- -----------------------------------------------------------------------
Functors and opposite categories.
----------------------------------------------------------------------- -/

/-! #brief Casting into OpCat OpCat.
-/
definition OpCat_OpCat.inFun (C : Cat.{ℓobj ℓhom})
    : Fun C (OpCat (OpCat C))
:= CastFun (eq.symm (OpCat_OpCat C))

/-! #brief Casting out of OpCat OpCat.
-/
definition OpCat_OpCat.outFun (C : Cat.{ℓobj ℓhom})
    : Fun (OpCat (OpCat C)) C
:= CastFun (OpCat_OpCat C)

/-! #brief OpCat_OpCat.inFun and OpCat_OpCat.outFun form a bijection.
-/
definition OpCat_OpCat.Bij (C : Cat.{ℓobj ℓhom})
    : Cat.Bij (OpCat_OpCat.inFun C) (OpCat_OpCat.outFun C)
:= CastFun.Bij _ _

/-! #brief The opposite functor.
-/
definition OpFun {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    (F : Fun C D)
    : Fun (OpCat C) (OpCat D)
:= { obj := λ c, F^.obj c
   , hom := λ c₁ c₂ f, F^.hom f
   , hom_id := λ c, F^.hom_id
   , hom_circ := λ c₁ c₂ c₃ g f, F^.hom_circ
   }

@[simp] theorem OpFun.simp_obj {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    (F : Fun C D)
    (x : (OpCat C)^.obj)
    : (OpFun F)^.obj x = F^.obj x
:= rfl

@[simp] theorem OpFun.simp_hom {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    (F : Fun C D)
    {x₁ x₂ : (OpCat C)^.obj} (f : (OpCat C)^.hom x₁ x₂)
    : (OpFun F)^.hom f = F^.hom f
:= rfl

/-! #brief The opposite functor preserves identity functors.
-/
theorem OpFun.id {C : Cat.{ℓobj ℓhom}}
    : OpFun (Fun.id C) = Fun.id (OpCat C)
:= begin
     apply Fun.eq,
     { intro c, trivial },
     { intros ωobj c₁ c₂ f, trivial }
   end

/-! #brief The opposite functor distributes over composition.
-/
theorem OpFun.comp {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    {G : Fun C D}
    {F : Fun B C}
    : OpFun (Fun.comp G F) = Fun.comp (OpFun G) (OpFun F)
:= begin
     apply Fun.eq,
     { intro c, trivial },
     { intros ωobj c₁ c₂ f, trivial }
   end

/-! #brief OpFun preserves bijections.
-/
theorem OpFun.Bij {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F : Fun C D} {G : Fun D C}
    (bij : Cat.Bij F G)
    : Cat.Bij (OpFun F) (OpFun G)
:= { id₁ := by calc OpFun G □□ OpFun F
                        = OpFun (G □□ F)   : by rw OpFun.comp
                    ... = OpFun (Fun.id C) : by rw bij^.id₁
                    ... = Fun.id (OpCat C) : by rw OpFun.id
   , id₂ := by calc OpFun F □□ OpFun G
                        = OpFun (F □□ G)   : by rw OpFun.comp
                    ... = OpFun (Fun.id D) : by rw bij^.id₂
                    ... = Fun.id (OpCat D) : by rw OpFun.id
   }

/-! #brief OpFun sends OpCat_OpCat.inFun to OpCat_OpCat.outFun.
-/
theorem OpFun.inFun {C : Cat.{ℓobj ℓhom}}
    : OpFun (OpCat_OpCat.inFun C) = OpCat_OpCat.outFun (OpCat C)
:= begin cases C, exact OpFun.id end

/-! #brief OpFun sends OpCat_OpCat.outFun to OpCat_OpCat.inFun.
-/
theorem OpFun.outFun {C : Cat.{ℓobj ℓhom}}
    : OpFun (OpCat_OpCat.outFun C) = OpCat_OpCat.inFun (OpCat C)
:= begin cases C, exact OpFun.id end

/-! #brief OpFun is nearly an involution.
-/
definition OpFun_OpFun.Conj {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    (F : Fun C D)
    : Fun.Conj _ _ _ _  F (OpFun (OpFun F))
:= { dom_bij := (OpCat_OpCat.Bij C)
   , codom_bij := (OpCat_OpCat.Bij D)
   , id₂ := begin
              apply Fun.eq,
              { intro c, cases C, cases D, trivial },
              { intros ωobj c₁ c₂ f, cases C, cases D, trivial }
            end
   }



/- -----------------------------------------------------------------------
Preservation of initial and final.
----------------------------------------------------------------------- -/

/-! #brief A functor which preserves final objects.
-/
class PresFinal {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    (F : Fun C D)
    : Type (max ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂)
:= (hom : ∀ [C_HasFinal : HasFinal C]
            (d : D^.obj)
          , D^.hom d (F^.obj (final C)))
   (pres : ∀ [C_HasFinal : HasFinal C]
           , IsFinal D (F^.obj (final C)) hom)

/-! #brief Functors which preserve final objects yield instances of HasFinal.
-/
instance PresFinal.HasFinal {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    [C_HasFinal : HasFinal C]
    (F : Fun C D) [F_PresFinal : PresFinal F]
    : HasFinal D
:= { obj := F^.obj (final C)
   , hom := PresFinal.hom F
   , final := PresFinal.pres F
   }

/-! #brief A functor which preserves initial objects.
-/
@[class] definition PresInit {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    (F : Fun C D)
    : Type (max ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂)
:= PresFinal (OpFun F)
-- := (hom : ∀ [C_HasInit : HasInit C]
--             (d : D^.obj)
--           , D^.hom (F^.obj (init C)) d)
--    (pres : ∀ [C_HasInit : HasInit C]
--            , IsInit D (F^.obj (init C)) hom)

/-! #brief Functors which preserve initial objects yield instances of HasInit.
-/
instance PresInit.HasInit {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    [C_HasInit : HasInit C]
    (F : Fun C D) [F_PresInit : PresInit F]
    : HasInit D
:= @PresFinal.HasFinal (OpCat C) (OpCat D) C_HasInit (OpFun F) F_PresInit



/- -----------------------------------------------------------------------
Functors and over and under categories.
----------------------------------------------------------------------- -/

/-! #brief Functor from OverCat.
-/
definition OverFun.out (C : Cat.{ℓobj₁ ℓhom₁}) (c : C^.obj)
    : Fun (OverCat C c) C
:= { obj := λ x, x^.obj
   , hom := λ x y f, f^.hom
   , hom_id := λ x, rfl
   , hom_circ := λ x y z g f, rfl
   }

/-! #brief Functors induce functors of over categories.
-/
definition OverFun {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    (X : C^.obj)
    (F : Fun C D)
    : Fun (OverCat C X) (OverCat D (F^.obj X))
:= { obj := λ A, OverObj.mk (F^.obj A^.dom) (F^.hom A^.down)
   , hom := λ A B f, OverHom.mk (F^.hom f^.hom) (by rw [f^.triangle, F^.hom_circ])
   , hom_id := λ A, OverHom.eq F^.hom_id
   , hom_circ := λ a b c g f, OverHom.eq F^.hom_circ
   }

/-! #brief Heterogeneous equality for OverFun.
-/
theorem OverFun.heq {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {X : C^.obj}
    : ∀ {F₁ F₂ : Fun C D}
         (ω : F₁ = F₂)
      , OverFun X F₁ == OverFun X F₂
| F .(F) (eq.refl .(F)) := heq.refl _

/-! #brief OverFun preserves identity functors.
-/
theorem OverFun.id {C : Cat.{ℓobj₁ ℓhom₁}} (X : C^.obj)
    : OverFun X (Fun.id C) = Fun.id (OverCat C X)
:= begin
     apply Fun.eq,
     { intro a, apply OverObj.eq,
       { trivial },
       { trivial }
     },
     { intros ωobj a b f,
       apply OverHom.heq (ωobj _) (ωobj _),
       { trivial }
     }
   end

/-! #brief OverFun distributes over composition of functors.
-/
theorem OverFun.comp {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    {X : B^.obj} {G : Fun C D} {F : Fun B C}
    : OverFun X (Fun.comp G F) = Fun.comp (OverFun (F^.obj X) G) (OverFun X F)
:= begin
     apply Fun.eq,
     { intro a, trivial },
     { intros ωobj a b f, trivial }
   end

/-! #brief Functors induce functors of under categories.
-/
definition UnderFun {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    (X : C^.obj)
    (F : Fun C D)
    : Fun (UnderCat C X) (UnderCat D (F^.obj X))
:= OpFun (@OverFun (OpCat C) (OpCat D) X (OpFun F))

/-! #brief UnderFun sends identity functors to identity functors.
-/
theorem UnderFun.id {C : Cat.{ℓobj₁ ℓhom₁}} (X : C^.obj)
    : UnderFun X (Fun.id C) = Fun.id (UnderCat C X)
:= by calc OpFun (@OverFun C⁻¹ C⁻¹ X (OpFun (Fun.id C)))
               = OpFun (@OverFun C⁻¹ C⁻¹ X (Fun.id C⁻¹)) : congr_arg OpFun (eq_of_heq (OverFun.heq OpFun.id))
           ... = OpFun (Fun.id (OverCat C⁻¹ X))          : congr_arg OpFun (OverFun.id X)
           ... = Fun.id (C\\X)                           : OpFun.id

/-! #brief UnderFun distributes over composition of functors.
-/
theorem UnderFun.comp {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    (X : B^.obj) (G : Fun C D) (F : Fun B C)
    : UnderFun X (Fun.comp G F) = Fun.comp (UnderFun (F^.obj X) G) (UnderFun X F)
:= by calc OpFun (@OverFun B⁻¹ D⁻¹ X (OpFun (G □□ F)))
               = OpFun (@OverFun B⁻¹ D⁻¹ X (OpFun G □□ OpFun F))                                       : congr_arg OpFun (eq_of_heq (OverFun.heq OpFun.comp))
           ... = OpFun (@OverFun C⁻¹ D⁻¹ ((OpFun F)^.obj X) (OpFun G) □□ @OverFun B⁻¹ C⁻¹ X (OpFun F)) : congr_arg OpFun (@OverFun.comp B⁻¹ C⁻¹ D⁻¹ X (OpFun G) (OpFun F))
           ... = OpFun (@OverFun C⁻¹ D⁻¹ (F^.obj X) (OpFun G)) □□ OpFun (@OverFun B⁻¹ C⁻¹ X (OpFun F)) : OpFun.comp

/-! #brief Under and over categories are dual concepts.
-/
definition Under_dual_Over (C : Cat.{ℓobj ℓhom}) (X : C^.obj)
    : UnderCat C X = OpCat (OverCat (OpCat C) X)
:= rfl

/-! #brief Over and under categories are dual concepts.
-/
definition Over_dual_Under (C : Cat.{ℓobj ℓhom}) (X : C^.obj)
    : OverCat C X = OpCat (UnderCat (OpCat C) X)
:= begin cases C, trivial end



/- -----------------------------------------------------------------------
Cone and co-cone categories.
----------------------------------------------------------------------- -/

/-! #brief An object in a cone category.
-/
structure Cone {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    (F : Fun C D)
    : Type (max ℓobj₁ ℓobj₂ ℓhom₂)
:= (obj : D^.obj)
   (hom : ∀ (c : C^.obj), D^.hom obj (F^.obj c))
   (comm : ∀ {c₁ c₂ : C^.obj} (f : C^.hom c₁ c₂)
           , hom c₂ = F^.hom f ∘∘ hom c₁)

/-! #brief Composition of a cone with a hom.
-/
definition Cone.circ {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F : Fun C D} (cone : Cone F)
    {d' : D^.obj} (h : D^.hom d' cone^.obj)
    : Cone F
:= { obj := d'
   , hom := λ c, D^.circ (cone^.hom c) h
   , comm := λ c₁ c₂ f
             , begin
                 rw D^.circ_assoc,
                 apply Cat.circ.congr_left,
                 apply cone^.comm
               end
   }

/-! #brief A hom in a cone category.
-/
structure ConeHom {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    (F : Fun C D)
    (X Y : Cone F)
    : Type ℓhom₂
:= (mediate : D^.hom X^.obj Y^.obj)
   (factor : ∀ (c : C^.obj), X^.hom c = Y^.hom c ∘∘ mediate)

/-! #brief Equality of homs in a cone category.
-/
theorem ConeHom.eq {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F : Fun C D}
    {X Y : Cone F}
    : ∀ {f₁ f₂ : ConeHom F X Y}
      , f₁^.mediate = f₂^.mediate
      → f₁ = f₂
| (ConeHom.mk f ω₁) (ConeHom.mk .(f) ω₂) (eq.refl .(f)) := rfl

/-! #brief An identity hom in a cone category.
-/
definition ConeHom.id {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F : Fun C D}
    (X : Cone F)
    : ConeHom F X X
:= { mediate := D^.id X^.obj
   , factor := λ c, eq.symm D^.circ_id_right
   }

@[simp] theorem ConeHom.id.simp_mediate {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F : Fun C D}
    {X : Cone F}
    : (ConeHom.id X)^.mediate = D^.id X^.obj
:= rfl

/-! #brief Composition of two homs in a cone category.
-/
definition ConeHom.comp {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F : Fun C D}
    {X Y Z : Cone F}
    (g : ConeHom F Y Z) (f : ConeHom F X Y)
    : ConeHom F X Z
:= { mediate := D^.circ g^.mediate f^.mediate
   , factor := λ c, by rw [D^.circ_assoc, -g^.factor, -f^.factor]
   }

@[simp] theorem ConeHom.comp.simp_mediate {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F : Fun C D}
    {X Y Z : Cone F}
    {g : ConeHom F Y Z} {f : ConeHom F X Y}
    : (ConeHom.comp g f)^.mediate = D^.circ g^.mediate f^.mediate
:= rfl

/-! #brief Composition of cone homs is associative.
-/
theorem ConeHom.comp_assoc {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F : Fun C D}
    {X Y Z W : Cone F}
    (h : ConeHom F Z W) (g : ConeHom F Y Z) (f : ConeHom F X Y)
    : ConeHom.comp h (ConeHom.comp g f) = ConeHom.comp (ConeHom.comp h g) f
:= ConeHom.eq D^.circ_assoc

/-! #brief Left-identity for cone hom composition.
-/
theorem ConeHom.comp_id_left {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F : Fun C D}
    {A B : Cone F} {f : ConeHom F A B}
    : ConeHom.comp (ConeHom.id B) f = f
:= ConeHom.eq D^.circ_id_left

/-! #brief Right-identity for cone hom composition.
-/
theorem ConeHom.comp_id_right {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F : Fun C D}
    {A B : Cone F} {f : ConeHom F A B}
    : ConeHom.comp f (ConeHom.id A) = f
:= ConeHom.eq D^.circ_id_right

/-! #brief A cone category.
-/
definition ConeCat {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    (F : Fun C D)
    : Cat.{(max ℓobj₁ ℓobj₂ ℓhom₂) (ℓhom₂ + 1)}
:= { obj := Cone F
   , hom := ConeHom F
   , id := ConeHom.id
   , circ := @ConeHom.comp C D F
   , circ_assoc := @ConeHom.comp_assoc C D F
   , circ_id_left := @ConeHom.comp_id_left C D F
   , circ_id_right := @ConeHom.comp_id_right C D F
   }

/-! #brief Equal functors give equal cone categories.
-/
definition ConeCat.CastFun {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F₁ F₂ : Fun C D}
    (ω : F₁ = F₂)
    : Fun (ConeCat F₁) (ConeCat F₂)
:= CastFun (congr_arg ConeCat ω)

/-! #brief A co-cone category.
-/
definition CoConeCat {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    (F : Fun C D)
    : Cat.{(max ℓobj₁ ℓobj₂ ℓhom₂) (ℓhom₂ + 1)}
:= ConeCat (OpFun F)

/-! #brief Equal functors give equal co-cone categories.
-/
definition CoConeCat.CastFun {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F₁ F₂ : Fun C D}
    (ω : F₁ = F₂)
    : Fun (CoConeCat F₁) (CoConeCat F₂)
:= CastFun (congr_arg CoConeCat ω)

/-! #brief An object in a co-cone category.
-/
definition CoCone {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    (F : Fun C D)
    : Type (max ℓobj₁ ℓobj₂ ℓhom₂)
:= (CoConeCat F)^.obj

/-! #brief Composition of a co-cone with a hom.
-/
definition CoCone.circ {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F : Fun C D} (ccone : CoCone F)
    {d' : D^.obj} (h : D^.hom ccone^.obj d')
    : CoCone F
:= Cone.circ ccone h

/-! #brief Construct an object in a co-cone category.
-/
definition CoCone.mk {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F : Fun C D}
    (d : D^.obj)
    (to : ∀ (c : C^.obj), D^.hom (F^.obj c) d)
    (ω : ∀ {c₁ c₂ : C^.obj} (f : C^.hom c₁ c₂)
         , to c₁ = to c₂ ∘∘ F^.hom f)
    : CoCone F
:= { obj := d
   , hom := to
   , comm := λ c₁ c₂, ω
   }

/-! #brief A hom in a co-cone category.
-/
definition CoConeHom {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    (F : Fun C D)
    (A B : CoCone F)
    : Type ℓhom₂
:= (CoConeCat F)^.hom A B

/-! #brief Construct a hom in a co-cone category.
-/
definition CoConeHom.mk {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F : Fun C D}
    {A B : CoCone F}
    (f : D^.hom B^.obj A^.obj)
    (ω : ∀ (c : C^.obj), A^.hom c = f ∘∘ B^.hom c)
    : CoConeHom F A B
:= { mediate := f
   , factor := ω
   }

/-! #brief Co-cones and cones are dual concepts.
-/
theorem CoCone_dual_Cone {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    (F : Fun C D)
    : CoConeCat F = ConeCat (OpFun F)
:= rfl

/-! #brief Cones and co-cones are dual concepts.
-/
theorem Cone_dual_CoCone {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    (F : Fun C D)
    : (ConeCat F) = (CoConeCat (OpFun F))
:= begin
     cases C, cases D, cases F,
     exact rfl,
   end



/- -----------------------------------------------------------------------
Functors and cone and co-cone categories.
----------------------------------------------------------------------- -/

/-! #brief Functors induce functors on cone categories by composition on the left.
-/
definition LeftConeFun {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    (G : Fun C D)
    (F : Fun B C)
    : Fun (ConeCat F) (ConeCat (G □□ F))
:= { obj := λ c, { obj := G^.obj c^.obj
                 , hom := λ a, G^.hom (c^.hom a)
                 , comm := λ a₁ a₂ f
                           , begin
                               rw [c^.comm f, G^.hom_circ],
                               trivial
                             end
                 }
   , hom := λ c₁ c₂ h, { mediate := G^.hom h^.mediate
                      , factor := λ b, begin dsimp, rw [h^.factor, G^.hom_circ] end
                      }
   , hom_id := λ c, ConeHom.eq G^.hom_id
   , hom_circ := λ c₁ c₂ c₃ g f, ConeHom.eq G^.hom_circ
   }

/-! #brief Functors induce functors on cone categories by composition on the right.
-/
definition RightConeFun {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    (G : Fun C D)
    (F : Fun B C)
    : Fun (ConeCat G) (ConeCat (G □□ F))
:= { obj := λ c, { obj := c^.obj
                 , hom := λ a, (c^.hom (F^.obj a))
                 , comm := λ a₁ a₂ f, c^.comm (F^.hom f)
                 }
   , hom := λ c₁ c₂ h, { mediate := h^.mediate
                      , factor := λ b, h^.factor (F^.obj b)
                      }
   , hom_id := λ c, rfl
   , hom_circ := λ c₁ c₂ c₃ g f, rfl
   }

/-! #brief Functors induce functors on cone categories by composition.
-/
definition ConeFun
    {A : Cat.{ℓobj₁ ℓhom₁}} {B : Cat.{ℓobj₂ ℓhom₂}} {C : Cat.{ℓobj₃ ℓhom₃}} {D : Cat.{ℓobj₄ ℓhom₄}}
    (H : Fun C D)
    (G : Fun B C)
    (F : Fun A B)
    : Fun (ConeCat G) (ConeCat (H □□ G □□ F))
:= Fun.comp (RightConeFun (Fun.comp H G) F) (LeftConeFun H G)

/-! #brief Functors induce functors on co-cone categories by composition on the left.
-/
definition LeftCoConeFun {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    (H : Fun C D)
    (F : Fun B C)
    : Fun (CoConeCat F) (CoConeCat (H □□ F))
:= LeftConeFun (OpFun H) (OpFun F)

/-! #brief Functors induce functors on co-cone categories by composition on the left.
-/
definition RightCoConeFun {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    (F : Fun C D)
    (H : Fun B C)
    : Fun (CoConeCat F) (CoConeCat (F □□ H))
:= RightConeFun (OpFun F) (OpFun H)

/-! #brief Functors induce functors on co-cone categories by composition.
-/
definition CoConeFun
    {A : Cat.{ℓobj₁ ℓhom₁}} {B : Cat.{ℓobj₂ ℓhom₂}} {C : Cat.{ℓobj₃ ℓhom₃}} {D : Cat.{ℓobj₄ ℓhom₄}}
    (H : Fun C D)
    (G : Fun B C)
    (F : Fun A B)
    : Fun (CoConeCat G) (CoConeCat (H □□ G □□ F))
:= ConeFun (OpFun H) (OpFun G) (OpFun F)

end qp
