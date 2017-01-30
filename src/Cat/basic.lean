/- ----------------------------------------------------------------------------
The basic definitions of category theory, together with the most fundamental
properties.
---------------------------------------------------------------------------- -/


namespace Qvr
universe variables ℓobj ℓhom ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂ ℓobj₃ ℓhom₃ ℓobj₄ ℓhom₄


/- ----------------------------------------------------------------------------
The three main notions in category theory are here defined: Cat, Fun, and
NatTrans.
---------------------------------------------------------------------------- -/

-- A strict category.
structure Cat : Type ((max ℓobj ℓhom) + 1)
:= (obj : Type ℓobj)
   (hom : ∀ (x y : obj)
          , Type ℓhom)
   (id : ∀ (x : obj)
         , hom x x)
   (circ : ∀ {x y z : obj}
           , hom y z → hom x y → hom x z)
   (circ_assoc : ∀ {x y z w : obj}
                   {h : hom z w} {g : hom y z} {f : hom x y}
                 , circ h (circ g f) = circ (circ h g) f)
   (circ_id_left : ∀ {x y : obj} {f : hom x y}
                   , circ (id y) f = f)
   (circ_id_right : ∀ {x y : obj} {f : hom x y}
                    , circ f (id x) = f)

attribute [simp] Cat.circ_id_left
attribute [simp] Cat.circ_id_right

-- Composition of hom's in a category.
-- \circ\circ
infixl `∘∘` : 150
:= λ {C : Cat} {x y z : C^.obj} (h : C^.hom y z) (f : C^.hom x y)
   , C^.circ h f


-- A functor between categories.
structure Fun (C : Cat.{ℓobj₁ ℓhom₁}) (D : Cat.{ℓobj₂ ℓhom₂})
  : Type ((max ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂) + 1)
:= (obj : C^.obj → D^.obj)
   (hom : ∀ {x y : C^.obj}
          , C^.hom x y → D^.hom (obj x) (obj y))
   (hom_id : ∀ {x : C^.obj}
             , hom (C^.id x) = D^.id (obj x))
   (hom_circ : ∀ {x y z : C^.obj}
                 {g : C^.hom y z} {f : C^.hom x y}
               , hom (g ∘∘ f) = hom g ∘∘ hom f)

attribute [simp] Fun.hom_id


-- A natural transformation between functors.
structure NatTrans
    {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    (F G : Fun C D)
  : Type ((max ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂) + 1)
:= (component : ∀ (x : C^.obj), D^.hom (F^.obj x) (G^.obj x))
   (transport : ∀ {x y : C^.obj} {f : C^.hom x y}
                , component y ∘∘ Fun.hom F f
                   = Fun.hom G f ∘∘ component x)



/- ----------------------------------------------------------------------------
Functors are morphisms of categories.
---------------------------------------------------------------------------- -/

-- TODO: Fix docstring!
--/-! #brief Helper for proving two functors are equal.
---/
theorem Fun.eq {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    : ∀ {F G : Fun C D}
        (ωobj : ∀ (x : C^.obj)
                , F^.obj x = G^.obj x)
        (ωhom : ∀ {x y : C^.obj} (f : C^.hom x y)
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
       apply ωhom
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
                , f₁ == f₂ → F₁^.hom f₁ == F₂^.hom f₂)
      , F₁ == F₂
| C D F₁ .C .D F₂ (eq.refl .C) (eq.refl .D) ωobj ωhom
:= begin
     apply heq_of_eq,
     apply Fun.eq,
     { intro x,
       apply eq_of_heq,
       apply ωobj,
       apply heq.refl
     },
     { intros x y f,
       apply ωhom,
       apply heq.refl
     }
   end

/-! #brief The identity functor.
-/
@[reducible] definition Fun.id (C : Cat.{ℓobj ℓhom}) : Fun.{ℓobj ℓhom ℓobj ℓhom} C C
:= { obj := λ x, x
   , hom := λ x y f, f
   , hom_id := λ x, rfl
   , hom_circ := λ x y z g f, rfl
   }

/-! #brief Composition of functors.
-/
@[reducible] definition Fun.comp {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    (G : Fun C D) (F : Fun B C)
    : Fun B D
:= { obj := λ x, G^.obj (F^.obj x)
   , hom := λ x y f, G^.hom (F^.hom f)
   , hom_id := λ x, by rw [F^.hom_id, G^.hom_id]
   , hom_circ := λ x y z g f, by rw [F^.hom_circ, G^.hom_circ]
   }

-- Composition of functors.
-- \Box\Box
infixl `□□` : 150
:= λ {B : Cat} {C : Cat} {D : Cat}
     (G : Fun C D) (F : Fun B C)
   , Fun.comp G F

/-! #brief Composition of functors is associative.
-/
theorem Fun.comp_assoc {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}} {E : Cat.{ℓobj₄ ℓhom₄}}
    {H : Fun D E} {G : Fun C D} {F : Fun B C}
    : H □□ (G □□ F) = (H □□ G) □□ F
:= rfl

/-! #brief The identity functor is a left-identity for composition.
-/
@[simp] theorem Fun.comp_id_left {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F : Fun C D}
    : Fun.id D □□ F = F
:= begin cases F, apply rfl end

/-! #brief The identity functor is a right-identity for composition.
-/
@[simp] theorem Fun.comp_id_right {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F : Fun C D}
    : F □□ Fun.id C = F
:= begin cases F, apply rfl end



/- ----------------------------------------------------------------------------
Natural transformations are morphisms of functors.
---------------------------------------------------------------------------- -/

/-! #brief Helper for proving two natural transformations are equal.
-/
theorem NatTrans.eq {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}} {F G : Fun C D}
    : ∀ {η₁ η₂ : NatTrans F G}
        (ωcomponent : ∀ (x : C^.obj)
                      , η₁^.component x = η₂^.component x)
      , η₁ = η₂
| (NatTrans.mk component₁ transport₁)
  (NatTrans.mk component₂ transport₂)
  ωcomponent
:= begin
     assert ωcomponent' : component₁ = component₂, { exact funext ωcomponent },
     subst ωcomponent'
   end

/-! #brief Helper for proving two natural transformations are heterogeneously equal.
-/
theorem NatTrans.heq
    : ∀ {C₁ : Cat.{ℓobj₁ ℓhom₁}} {D₁ : Cat.{ℓobj₂ ℓhom₂}} {F₁ G₁ : Fun C₁ D₁}
        {C₂ : Cat.{ℓobj₁ ℓhom₁}} {D₂ : Cat.{ℓobj₂ ℓhom₂}} {F₂ G₂ : Fun C₂ D₂}
        {η₁ : NatTrans F₁ G₁} {η₂ : NatTrans F₂ G₂}
        (ωC : C₁ = C₂) (ωD : D₁ = D₂) (ωF : F₁ == F₂) (ωG : G₁ == G₂)
        (ωcomponent : ∀ (x₁ : C₁^.obj) (x₂ : C₂^.obj)
                      , x₁ == x₂ → η₁^.component x₁ == η₂^.component x₂)
      , η₁ == η₂
| C D F G .C .D .F .G η₁ η₂
  (eq.refl .C) (eq.refl .D) (heq.refl .F) (heq.refl .G)
  ωcomponent
:= begin
     apply heq_of_eq,
     apply NatTrans.eq,
     intro x,
     apply eq_of_heq,
     apply ωcomponent,
     apply heq.refl
   end

/-! #brief The identity natural transformation.
-/
@[reducible] definition NatTrans.id {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    (F : Fun C D)
    : NatTrans F F
:= { component := λ x, D^.id (F^.obj x)
   , transport
      := λ x y f
         , by calc D^.id (F^.obj y) ∘∘ F^.hom f
                       = F^.hom f                     : D^.circ_id_left
                   ... = F^.hom f ∘∘ D^.id (F^.obj x) : eq.symm D^.circ_id_right
   }

/-! #brief Composition of natural transformations.
-/
@[reducible] definition NatTrans.comp {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F G H : Fun C D}
    (ηGH : NatTrans G H) (ηFG : NatTrans F G)
    : NatTrans F H
:= { component := λ x, ηGH^.component x ∘∘ ηFG^.component x
   , transport
      := λ x y f
         , by calc (ηGH^.component y ∘∘ ηFG^.component y) ∘∘ F^.hom f
                       = ηGH^.component y ∘∘ (ηFG^.component y ∘∘ F^.hom f) : eq.symm D^.circ_assoc
                   ... = ηGH^.component y ∘∘ (G^.hom f ∘∘ ηFG^.component x) : by rw ηFG^.transport
                   ... = (ηGH^.component y ∘∘ G^.hom f) ∘∘ ηFG^.component x : D^.circ_assoc
                   ... = (H^.hom f ∘∘ ηGH^.component x) ∘∘ ηFG^.component x : by rw ηGH^.transport
                   ... = H^.hom f ∘∘ (ηGH^.component x ∘∘ ηFG^.component x) : eq.symm D^.circ_assoc
   }

-- Composition of natural transformations.
-- \Diamond\Diamond
infixl `◇◇` : 150
:= λ {C : Cat} {D : Cat} {F G H : Fun C D}
     (ηGH : NatTrans G H) (ηFG : NatTrans F G)
   , NatTrans.comp ηGH ηFG

/-! #brief Composition of natural transformations is associative.
-/
theorem NatTrans.comp_assoc {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F G H J : Fun C D}
    {ηHJ : NatTrans H J} {ηGH : NatTrans G H} {ηFG : NatTrans F G}
    : ηHJ ◇◇ (ηGH ◇◇ ηFG) = (ηHJ ◇◇ ηGH) ◇◇ ηFG
:= begin
     apply NatTrans.eq,
     intro x,
     simp,
     apply D^.circ_assoc
   end

/-! #brief The identity natural transformation is a left-identity for composition.
-/
@[simp] theorem NatTrans.comp_id_left {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F G : Fun C D} {ηFG : NatTrans F G}
    : NatTrans.id G ◇◇ ηFG = ηFG
:= begin
     apply NatTrans.eq,
     intro x,
     simp,
     apply D^.circ_id_left
   end

/-! #brief The identity natural transformation is a right-identity for composition.
-/
@[simp] theorem NatTrans.comp_id_right {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F G : Fun C D} {ηFG : NatTrans F G}
    : ηFG ◇◇ NatTrans.id F = ηFG
:= begin
     apply NatTrans.eq,
     intro x,
     simp,
     apply D^.circ_id_right
   end

/-! #brief Natural transformations can be composed with functors on the left.
-/
@[reducible] definition NatTrans.fun_comp {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    {F₁ F₂ : Fun B C}
    (G : Fun C D) (η : NatTrans F₁ F₂)
    : NatTrans (G □□ F₁) (G □□ F₂)
:= { component := λ x, G^.hom (η^.component x)
   , transport
      := λ x y f
         , by calc G^.hom (η^.component y) ∘∘ (G □□ F₁)^.hom f
                       = G^.hom (η^.component y ∘∘ F₁^.hom f)        : eq.symm G^.hom_circ
                   ... = G^.hom (F₂^.hom f ∘∘ η^.component x)        : by rw η^.transport
                   ... = (G □□ F₂)^.hom f ∘∘ G^.hom (η^.component x) : G^.hom_circ
   }

-- Composition of a functor with a natural transformation.
-- \Box\Diamond
infix `□◇` : 150
:= λ {B : Cat} {C : Cat} {D : Cat}
     {F₁ F₂ : Fun B C}
     (G : Fun C D) (η : NatTrans F₁ F₂)
   , NatTrans.fun_comp G η

/-! #brief Fun.id is a left-identity for NatTrans.fun_comp.
-/
@[simp] theorem NatTrans.fun_comp_id_left {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F₁ F₂ : Fun C D} {η : NatTrans F₁ F₂}
    : Fun.id D □◇ η == η
:= begin
     apply NatTrans.heq rfl rfl (heq_of_eq Fun.comp_id_left) (heq_of_eq Fun.comp_id_left),
     intros x₁ x₂ ωx,
     simp,
     cases ωx,
     apply heq.refl
   end

/-! #brief Functors composed with NatTrans.id on the right get absorbed.
-/
@[simp] theorem NatTrans.fun_comp_id_right {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    {G : Fun C D} {F : Fun B C}
    : G □◇ NatTrans.id F = NatTrans.id (G □□ F)
:= begin
     apply NatTrans.eq,
     intro x,
     simp
   end

/-! #brief NatTrans.fun_comp distributes over Fun.comp.
-/
@[simp] theorem NatTrans.fun_comp_dist_left {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}} {E : Cat.{ℓobj₄ ℓhom₄}}
    {H : Fun D E} {G : Fun C D} {F₁ F₂ : Fun B C} {η : NatTrans F₁ F₂}
    : H □◇ (G □◇ η) = (H □□ G) □◇ η
:= by simp

/-! #brief Natural transformations can be composed with functors on the right.
-/
@[reducible] definition NatTrans.comp_fun {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    {G₁ G₂ : Fun C D}
    (η : NatTrans G₁ G₂) (F : Fun B C)
    : NatTrans (G₁ □□ F) (G₂ □□ F)
:= { component := λ x, η^.component (F^.obj x)
   , transport := λ x y f, η^.transport
   }

-- Composition of a natural transformation with a functor.
-- \Diamond\Box
infix `◇□` : 150
:= λ {B : Cat} {C : Cat} {D : Cat}
     {G₁ G₂ : Fun C D}
     (η : NatTrans G₁ G₂) (F : Fun B C)
   , NatTrans.comp_fun η F

/-! #brief Functors composed with NatTrans.id on the left get absorbed.
-/
@[simp] theorem NatTrans.comp_fun_id_left {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    {G : Fun C D} {F : Fun B C}
    : NatTrans.id G ◇□ F = NatTrans.id (G □□ F)
:= by simp

/-! #brief Fun.id is a right-identity for NatTrans.comp_fun.
-/
@[simp] theorem NatTrans.comp_fun_id_right {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F₁ F₂ : Fun C D} {η : NatTrans F₁ F₂}
    : η ◇□ Fun.id C == η
:= by simp

/-! #brief NatTrans.comp_fun distributes over Fun.comp.
-/
@[simp] theorem NatTrans.comp_fun_dist_right {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}} {E : Cat.{ℓobj₄ ℓhom₄}}
    {H₁ H₂ : Fun D E} {G : Fun C D} {F : Fun B C} {η : NatTrans H₁ H₂}
    : (η ◇□ G) ◇□ F = η ◇□ (G □□ F)
:= by simp



/- ----------------------------------------------------------------------------
Some important categories.
---------------------------------------------------------------------------- -/

/-! #brief The category of categories at level {ℓobj ℓhom} and functors between them.
-/
@[reducible] definition CatCat : Cat.{((max ℓobj ℓhom) + 1) ((max ℓobj ℓhom) + 1)}
:= { obj := Cat.{ℓobj ℓhom}
   , hom := Fun.{ℓobj ℓhom ℓobj ℓhom}
   , id := Fun.id
   , circ := @Fun.comp
   , circ_assoc := @Fun.comp_assoc
   , circ_id_left := @Fun.comp_id_left
   , circ_id_right := @Fun.comp_id_right
   }

/-! #brief The category of functors and natural transformations between them.
-/
@[reducible] definition FunCat (C : Cat.{ℓobj₁ ℓhom₁}) (D : Cat.{ℓobj₂ ℓhom₂})
    : Cat.{((max ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂) + 1) ((max ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂) + 1)}
:= { obj := Fun C D
   , hom := NatTrans
   , id := NatTrans.id
   , circ := @NatTrans.comp _ _
   , circ_assoc := @NatTrans.comp_assoc _ _
   , circ_id_left := @NatTrans.comp_id_left _ _
   , circ_id_right := @NatTrans.comp_id_right _ _
   }

/-! #brief The category of propositions and implications between them.
-/
@[reducible] definition PropCat : Cat.{1 0}
:= { obj := Prop
   , hom := λ P Q, P → Q
   , id := λ P ω, ω
   , circ := λ P Q R g f ω, g (f ω)
   , circ_assoc := λ P Q R S h g f, rfl
   , circ_id_left := λ P Q f, rfl
   , circ_id_right := λ P Q f, rfl
   }

/-! #brief The category of Lean terms in Type {ℓ+1} and functions between them.
-/
@[reducible] definition {ℓ} LeanCat : Cat.{(ℓ + 2) (ℓ + 1)}
:= { obj := Type.{ℓ + 1}
   , hom := λ X Y, X → Y
   , id := λ X x, x
   , circ := λ X Y Z g f x, g (f x)
   , circ_assoc := λ X Y Z W h g f, rfl
   , circ_id_left := λ X Y f, rfl
   , circ_id_right := λ X Y f, rfl
   }

/-! #brief The opposite category.
-/
@[reducible] definition OpCat (C : Cat.{ℓobj ℓhom}) : Cat.{ℓobj ℓhom}
:= { obj := C^.obj
   , hom := λ x y, C^.hom y x
   , id := λ x, C^.id x
   , circ := λ x y z g f, f ∘∘ g
   , circ_assoc := λ x y z w h g f, eq.symm C^.circ_assoc
   , circ_id_left := λ x y f, C^.circ_id_right
   , circ_id_right := λ x y f, C^.circ_id_left
   }



/- ----------------------------------------------------------------------------
Boxed morphisms.
---------------------------------------------------------------------------- -/

namespace Cat
-- A hom in a category, boxed up with its domain and codomain.
structure BxHom (C : Cat.{ℓobj ℓhom}) : Type (max 1 ℓobj ℓhom)
:= (dom : C^.obj)
   (codom : C^.obj)
   (hom : C^.hom dom codom)

-- TODO: Fix docstring!
-- /-! #brief An equality helper for `BxHom.
-- -/
theorem BxHom.eq {C : Cat}
  : ∀ (h₁ h₂ : BxHom C)
    , h₁^.dom   =  h₂^.dom
    → h₁^.codom =  h₂^.codom
    → h₁^.hom   == h₂^.hom
    → h₁ = h₂
| (BxHom.mk dom₁ codom₁ hom₁)
  (BxHom.mk .dom₁ .codom₁ .hom₁)
  (eq.refl .dom₁) (eq.refl .codom₁) (heq.refl .hom₁)
  := rfl
end Cat

end Qvr
