/- ----------------------------------------------------------------------------
The basic definitions of category theory, together with the most fundamental
properties.
---------------------------------------------------------------------------- -/

import ..util

namespace qp
universe variables ℓ ℓobj ℓhom ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂ ℓobj₃ ℓhom₃ ℓobj₄ ℓhom₄



/- ----------------------------------------------------------------------------
The three main notions in category theory are here defined: Cat, Fun, and
NatTrans.
---------------------------------------------------------------------------- -/

-- A strict category.
structure Cat : Type ((max ℓobj ℓhom) + 1)
:= (obj : Type ℓobj)
   (hom : ∀ (x y : obj)
          , Sort ℓhom)
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

-- An object in a category.
-- [[ ]]
notation `[[` C `]]` := Cat.obj C

-- The identity hom at an object.
-- \langle\langle \rangle\rangle
notation `⟨⟨` x `⟩⟩` := Cat.id _ x

-- A hom in a category.
-- \to\to
infix `→→` : 110 := Cat.hom _

-- Composition of hom's in a category.
-- \o\o
infixl `∘∘` : 150 := Cat.circ _

-- A functor between categories.
structure Fun (C : Cat.{ℓobj₁ ℓhom₁}) (D : Cat.{ℓobj₂ ℓhom₂})
    : Type (max ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂)
:= (obj : [[C]] → [[D]])
   (hom : ∀ {x y : [[C]]}, x →→ y → obj x →→ obj y)
   (hom_id : ∀ {x : [[C]]}, hom ⟨⟨x⟩⟩ = ⟨⟨obj x⟩⟩)
   (hom_circ : ∀ {x y z : [[C]]}
                 {g : y →→ z} {f : x →→ y}
               , hom (g ∘∘ f) = hom g ∘∘ hom f)

attribute [simp] Fun.hom_id

-- A functor between categories.
-- \rightrightarrows\rightrightarrows
infix `⇉⇉` : 120 := Fun

/-! #brief Every functor can be treated as a function on objects.
-/
@[reducible] instance Fun.obj_has_coe_to_fun {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    : has_coe_to_fun (C ⇉⇉ D)
:= { F := λ G, [[C]] → [[D]]
   , coe := λ G x, G^.obj x
   }

-- Action of a functor on a hom.
-- \nearrow
infix `↗` : 100 := Fun.hom -- λ {C : Cat} {D : Cat} (F : C ⇉⇉ D) {x y : [[C]]} (f : x →→ y), F^.hom f

-- A natural transformation between functors.
structure NatTrans
    {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    (F G : C ⇉⇉ D)
    : Type (max ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂)
:= (component : ∀ (x : [[C]]), F x →→ G x)
   (transport : ∀ {x y : [[C]]} {f : x →→ y}
                , component y ∘∘ (F^.hom f)
                   = (G^.hom f) ∘∘ component x)

-- A natural transformation.
-- \rightarrowtail\rightarrowtail
infix `↣↣` : 110 := NatTrans

/-! #brief Every natural transformation can be treated as a function on objects.
-/
@[reducible] instance NatTrans.obj_has_coe_to_fun {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F₁ F₂ : C ⇉⇉ D}
    : has_coe_to_fun (F₁ ↣↣ F₂)
:= { F := λ η, ∀ (x : [[C]]), F₁ x →→ F₂ x
   , coe := λ η x, η^.component x
   }



/- ----------------------------------------------------------------------------
Functors are morphisms of categories.
---------------------------------------------------------------------------- -/

/-! #brief Helper for proving two functors are equal.
-/
theorem Fun.eq {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    : ∀ {F G : C ⇉⇉ D}
        (ωobj : ∀ (x : [[C]])
                , F x = G x)
        (ωhom : ∀ {x y : [[C]]} (f : x →→ y)
                , F ↗ f == G ↗ f)
      , F = G
| (Fun.mk Fobj Fhom Fhom_id Fhom_circ)
  (Fun.mk Gobj Ghom Ghom_id Ghom_circ)
  ωobj ωhom
:= begin
     assert ωobj' : Fobj = Gobj, { exact pfunext ωobj },
     subst ωobj',
     assert ωhom' : @Fhom = @Ghom,
     { apply pfunext, intro x,
       apply pfunext, intro y,
       apply pfunext, intro f,
       apply eq_of_heq,
       apply ωhom
     },
     subst ωhom'
   end

/-! #brief Helper for proving two functors are heterogeneously equal.
-/
theorem Fun.heq
    : ∀ {C₁ : Cat.{ℓobj₁ ℓhom₁}} {D₁ : Cat.{ℓobj₂ ℓhom₂}} {F₁ : C₁ ⇉⇉ D₁}
        {C₂ : Cat.{ℓobj₁ ℓhom₁}} {D₂ : Cat.{ℓobj₂ ℓhom₂}} {F₂ : C₂ ⇉⇉ D₂}
        (ωC : C₁ = C₂) (ωD : D₁ = D₂)
        (ωobj : ∀ (x₁ : [[C₁]]) (x₂ : [[C₂]])
                , x₁ == x₂ → F₁ x₁ == F₂ x₂)
        (ωhom : ∀ (x₁ y₁ : [[C₁]]) (x₂ y₂ : [[C₂]])
                  (f₁ : x₁ →→ y₁) (f₂ : x₂ →→ y₂)
                , f₁ == f₂ → (F₁ ↗ f₁) == (F₂ ↗ f₂))
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
definition Fun.id (C : Cat.{ℓobj ℓhom}) : Fun.{ℓobj ℓhom ℓobj ℓhom} C C
:= { obj := λ x, x
   , hom := λ x y f, f
   , hom_id := λ x, rfl
   , hom_circ := λ x y z g f, rfl
   }

@[simp] theorem Fun.id.simp_obj {C : Cat.{ℓobj ℓhom}}
    (c : [[C]])
    : Fun.id C c = c
:= rfl

@[simp] theorem Fun.id.simp_hom {C : Cat.{ℓobj ℓhom}}
    {c₁ c₂ : [[C]]} (f : c₁ →→ c₂)
    : Fun.id C ↗ f = f
:= rfl

/-! #brief Composition of functors.
-/
definition Fun.comp {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    (G : C ⇉⇉ D) (F : B ⇉⇉ C)
    : B ⇉⇉ D
:= { obj := λ x, G (F x)
   , hom := λ x y f, G ↗ (F ↗ f)
   , hom_id := λ x, begin dsimp, simp end
   , hom_circ := λ x y z g f, begin dsimp, simp [Fun.hom_circ] end
   }

-- Composition of functors.
-- \Box\Box
infixl `□□` : 150 := Fun.comp

@[simp] theorem Fun.comp.simp_obj {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    (G : C ⇉⇉ D) (F : B ⇉⇉ C) (x : [[B]])
    : (G □□ F) x = G (F x)
:= rfl

@[simp] theorem Fun.comp.simp_hom {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    (G : C ⇉⇉ D) (F : B ⇉⇉ C) {x₁ x₂ : [[B]]} (f : x₁ →→ x₂)
    : (G □□ F) ↗ f = G ↗ (F ↗ f)
:= rfl

/-! #brief Composition of functors is associative.
-/
theorem Fun.comp_assoc {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}} {E : Cat.{ℓobj₄ ℓhom₄}}
    {H : D ⇉⇉ E} {G : C ⇉⇉ D} {F : B ⇉⇉ C}
    : H □□ (G □□ F) = (H □□ G) □□ F
:= begin
     apply Fun.eq,
     { intro b, repeat {rw [Fun.comp.simp_obj]} },
     { intros x y f, repeat {rw [Fun.comp.simp_hom]}, apply heq.refl }
   end

/-! #brief The identity functor is a left-identity for composition.
-/
@[simp] theorem Fun.comp_id_left {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F : C ⇉⇉ D}
    : Fun.id D □□ F = F
:= begin
     apply Fun.eq,
     { intro x, rw [Fun.comp.simp_obj, Fun.id.simp_obj] },
     { intros x y f, rw [Fun.comp.simp_hom, Fun.id.simp_hom], apply heq.refl }
   end

/-! #brief The identity functor is a right-identity for composition.
-/
@[simp] theorem Fun.comp_id_right {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F : C ⇉⇉ D}
    : F □□ Fun.id C = F
:= begin
     apply Fun.eq,
     { intro x, rw [Fun.comp.simp_obj, Fun.id.simp_obj] },
     { intros x y f, rw [Fun.comp.simp_hom, Fun.id.simp_hom], apply heq.refl }
   end



/- ----------------------------------------------------------------------------
Natural transformations are morphisms of functors.
---------------------------------------------------------------------------- -/

/-! #brief Helper for proving two natural transformations are equal.
-/
theorem NatTrans.eq {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}} {F G : C ⇉⇉ D}
    : ∀ {η₁ η₂ : F ↣↣ G}
        (ωcomponent : ∀ (x : [[C]])
                      , η₁ x = η₂ x)
      , η₁ = η₂
| (NatTrans.mk component₁ transport₁)
  (NatTrans.mk component₂ transport₂)
  ωcomponent
:= begin
     assert ωcomponent' : component₁ = component₂, { exact pfunext ωcomponent },
     subst ωcomponent'
   end

/-! #brief Helper for proving two natural transformations are heterogeneously equal.
-/
theorem NatTrans.heq
    : ∀ {C₁ : Cat.{ℓobj₁ ℓhom₁}} {D₁ : Cat.{ℓobj₂ ℓhom₂}} {F₁ G₁ : C₁ ⇉⇉ D₁}
        {C₂ : Cat.{ℓobj₁ ℓhom₁}} {D₂ : Cat.{ℓobj₂ ℓhom₂}} {F₂ G₂ : C₂ ⇉⇉ D₂}
        {η₁ : F₁ ↣↣ G₁} {η₂ : F₂ ↣↣ G₂}
        (ωC : C₁ = C₂) (ωD : D₁ = D₂) (ωF : F₁ == F₂) (ωG : G₁ == G₂)
        (ωcomponent : ∀ (x₁ : [[C₁]]) (x₂ : [[C₂]])
                      , x₁ == x₂ → η₁ x₁ == η₂ x₂)
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
definition NatTrans.id {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    (F : C ⇉⇉ D)
    : F ↣↣ F
:= { component := λ x, ⟨⟨F x⟩⟩
   , transport
      := λ x y f
         , by calc ⟨⟨F y⟩⟩ ∘∘ (F ↗ f)
                       = (F ↗ f)            : D^.circ_id_left
                   ... = (F ↗ f) ∘∘ ⟨⟨F x⟩⟩ : eq.symm D^.circ_id_right
   }

@[simp] theorem NatTrans.id.simp_component {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    (F : C ⇉⇉ D) (x : [[C]])
    : (NatTrans.id F) x = ⟨⟨F x⟩⟩
:= rfl

/-! #brief Vertical composition of natural transformations.
-/
definition NatTrans.comp {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F G H : C ⇉⇉ D}
    (ηGH : G ↣↣ H) (ηFG : F ↣↣ G)
    : F ↣↣ H
:= { component := λ x, ηGH x ∘∘ ηFG x
   , transport
      := λ x y f
         , by calc (ηGH y ∘∘ ηFG y) ∘∘ (F ↗ f)
                       = ηGH y ∘∘ (ηFG y ∘∘ (F ↗ f)) : eq.symm D^.circ_assoc
                   ... = ηGH y ∘∘ ((G ↗ f) ∘∘ ηFG x) : by rw ηFG^.transport
                   ... = (ηGH y ∘∘ (G ↗ f)) ∘∘ ηFG x : D^.circ_assoc
                   ... = ((H ↗ f) ∘∘ ηGH x) ∘∘ ηFG x : by rw ηGH^.transport
                   ... = (H ↗ f) ∘∘ (ηGH x ∘∘ ηFG x) : eq.symm D^.circ_assoc
   }

-- Composition of natural transformations.
-- \Diamond\Diamond
infixl `◇◇` : 150 := NatTrans.comp

@[simp] theorem NatTrans.comp.simp_component {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F G H : C ⇉⇉ D}
    (ηGH : G ↣↣ H) (ηFG : F ↣↣ G)
    (x : [[C]])
    : (ηGH ◇◇ ηFG) x = ηGH x ∘∘ ηFG x
:= rfl

/-! #brief Composition of natural transformations is associative.
-/
theorem NatTrans.comp_assoc {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F G H J : C ⇉⇉ D}
    {ηHJ : H ↣↣ J} {ηGH : G ↣↣ H} {ηFG : F ↣↣ G}
    : ηHJ ◇◇ (ηGH ◇◇ ηFG) = (ηHJ ◇◇ ηGH) ◇◇ ηFG
:= begin
     apply NatTrans.eq,
     intro x,
     repeat { rw [NatTrans.comp.simp_component] },
     apply Cat.circ_assoc
   end

/-! #brief The identity natural transformation is a left-identity for composition.
-/
@[simp] theorem NatTrans.comp_id_left {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F G : C ⇉⇉ D} {ηFG : F ↣↣ G}
    : NatTrans.id G ◇◇ ηFG = ηFG
:= begin
     apply NatTrans.eq,
     intro x,
     rw [NatTrans.comp.simp_component, NatTrans.id.simp_component],
     simp
   end

/-! #brief The identity natural transformation is a right-identity for composition.
-/
@[simp] theorem NatTrans.comp_id_right {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F G : C ⇉⇉ D} {ηFG : F ↣↣ G}
    : ηFG ◇◇ NatTrans.id F = ηFG
:= begin
     apply NatTrans.eq,
     intro x,
     rw [NatTrans.comp.simp_component, NatTrans.id.simp_component],
     simp
   end

/-! #brief Natural transformations can be composed with functors on the left.
-/
definition NatTrans.fun_comp {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    {F₁ F₂ : B ⇉⇉ C}
    (G : C ⇉⇉ D) (η : F₁ ↣↣ F₂)
    : (G □□ F₁) ↣↣ (G □□ F₂)
:= { component := λ x, G ↗ (η x)
   , transport
      := λ x y f
         , by calc (G ↗ (η y)) ∘∘ ((G □□ F₁)^.hom f)
                       = G ↗ (η y ∘∘ (F₁ ↗ f))         : eq.symm G^.hom_circ
                   ... = G ↗ ((F₂ ↗ f) ∘∘ η x)         : by rw η^.transport
                   ... = ((G □□ F₂)^.hom f) ∘∘ (G ↗ (η x)) : G^.hom_circ
   }

-- Composition of a functor with a natural transformation.
-- \Box\Diamond
infix `□◇` : 150
:= λ {B : Cat} {C : Cat} {D : Cat}
     {F₁ F₂ : B ⇉⇉ C}
     (G : C ⇉⇉ D) (η : F₁ ↣↣ F₂)
   , NatTrans.fun_comp G η

@[simp] theorem NatTrans.fun_comp.simp_component {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    {F₁ F₂ : B ⇉⇉ C}
    (G : C ⇉⇉ D) (η : F₁ ↣↣ F₂)
    (x : [[B]])
    : (G □◇ η) x = G ↗ (η x)
:= rfl

/-! #brief Fun.id is a left-identity for NatTrans.fun_comp.
-/
@[simp] theorem NatTrans.fun_comp_id_left {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F₁ F₂ : C ⇉⇉ D} {η : F₁ ↣↣ F₂}
    : Fun.id D □◇ η == η
:= begin
     apply NatTrans.heq rfl rfl (heq_of_eq Fun.comp_id_left) (heq_of_eq Fun.comp_id_left),
     intros x₁ x₂ ωx,
     cases ωx,
     apply heq.refl
   end

/-! #brief Functors composed with NatTrans.id on the right get absorbed.
-/
@[simp] theorem NatTrans.fun_comp_id_right {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    {G : C ⇉⇉ D} {F : B ⇉⇉ C}
    : G □◇ NatTrans.id F = NatTrans.id (G □□ F)
:= begin
     apply NatTrans.eq,
     intro x,
     simp,
     apply rfl
   end

/-! #brief NatTrans.fun_comp distributes over Fun.comp.
-/
theorem NatTrans.fun_comp_dist_left {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}} {E : Cat.{ℓobj₄ ℓhom₄}}
    {H : D ⇉⇉ E} {G : C ⇉⇉ D} {F₁ F₂ : B ⇉⇉ C} {η : F₁ ↣↣ F₂}
    : H □◇ (G □◇ η) = (H □□ G) □◇ η
:= begin
     apply NatTrans.eq,
     intro x,
     apply rfl
   end

/-! #brief Natural transformations can be composed with functors on the right.
-/
definition NatTrans.comp_fun {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    {G₁ G₂ : C ⇉⇉ D}
    (η : G₁ ↣↣ G₂) (F : B ⇉⇉ C)
    : (G₁ □□ F) ↣↣ (G₂ □□ F)
:= { component := λ x, η (F x)
   , transport := λ x y f, η^.transport
   }

-- Composition of a natural transformation with a functor.
-- \Diamond\Box
infix `◇□` : 150
:= λ {B : Cat} {C : Cat} {D : Cat}
     {G₁ G₂ : C ⇉⇉ D}
     (η : G₁ ↣↣ G₂) (F : B ⇉⇉ C)
   , NatTrans.comp_fun η F

@[simp] theorem NatTrans.comp_fun.simp_component {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    {G₁ G₂ : C ⇉⇉ D}
    (η : G₁ ↣↣ G₂) (F : B ⇉⇉ C)
    (x : [[B]])
    : (η ◇□ F) x = η (F x)
:= rfl

/-! #brief Functors composed with NatTrans.id on the left get absorbed.
-/
@[simp] theorem NatTrans.comp_fun_id_left {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    {G : C ⇉⇉ D} {F : B ⇉⇉ C}
    : NatTrans.id G ◇□ F = NatTrans.id (G □□ F)
:= begin
     apply NatTrans.eq,
     intro x,
     apply rfl
   end

/-! #brief Fun.id is a right-identity for NatTrans.comp_fun.
-/
@[simp] theorem NatTrans.comp_fun_id_right {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F₁ F₂ : C ⇉⇉ D} {η : F₁ ↣↣ F₂}
    : η ◇□ Fun.id C == η
:= begin
     apply NatTrans.heq rfl rfl,
     { simp },
     { simp },
     { intros x₁ x₂ ωx, cases ωx, apply heq.refl }
   end

/-! #brief NatTrans.comp_fun distributes over Fun.comp.
-/
theorem NatTrans.comp_fun_dist_right {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}} {E : Cat.{ℓobj₄ ℓhom₄}}
    {H₁ H₂ : D ⇉⇉ E} {G : C ⇉⇉ D} {F : B ⇉⇉ C} {η : H₁ ↣↣ H₂}
    : (η ◇□ G) ◇□ F = η ◇□ (G □□ F)
:= begin
     apply NatTrans.eq,
     intro x,
     apply rfl
   end



/- ----------------------------------------------------------------------------
Boxed homs.
---------------------------------------------------------------------------- -/

namespace Cat
-- A hom in a category, boxed up with its domain and codomain.
structure BxHom (C : Cat.{ℓobj ℓhom}) : Type (max ℓobj ℓhom)
:= (dom : [[C]])
   (codom : [[C]])
   (hom : dom →→ codom)

/-! #brief An equality helper for `BxHom.
-/
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



/- ----------------------------------------------------------------------------
Finite categories.
---------------------------------------------------------------------------- -/

-- A finite category.
class Cat.Fin (C : Cat.{ℓobj ℓhom}) : Type ((max ℓobj ℓhom) + 1)
:= (obj : FinType [[C]])
   (hom : ∀ (x y : [[C]]), FinType (x →→ y))



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
    : Cat--.{((max ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂) + 1) ((max ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂) + 1)}
:= { obj := C ⇉⇉ D
   , hom := NatTrans
   , id := NatTrans.id
   , circ := @NatTrans.comp _ _
   , circ_assoc := @NatTrans.comp_assoc _ _
   , circ_id_left := @NatTrans.comp_id_left _ _
   , circ_id_right := @NatTrans.comp_id_right _ _
   }

/-! #brief The opposite category.
-/
@[reducible] definition OpCat (C : Cat.{ℓobj ℓhom}) : Cat.{ℓobj ℓhom}
:= { obj := [[C]]
   , hom := λ x y, y →→ x
   , id := λ x, ⟨⟨x⟩⟩
   , circ := λ x y z g f, f ∘∘ g
   , circ_assoc := λ x y z w h g f, eq.symm C^.circ_assoc
   , circ_id_left := λ x y f, C^.circ_id_right
   , circ_id_right := λ x y f, C^.circ_id_left
   }

-- The opposite category.
-- {{}}\inv
notation `{{` C `}}⁻¹` := OpCat C

/-! #brief The opposite functor.
-/
definition OpFun {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    (F : C ⇉⇉ D)
    : {{C}}⁻¹ ⇉⇉ {{D}}⁻¹
:= { obj := F^.obj
   , hom := λ x y f, F^.hom f
   , hom_id := λ x, F^.hom_id
   , hom_circ := λ x y z g f, F^.hom_circ
   }

/-! #brief OpFun maps the identity functor to the identity functor.
-/
@[simp] theorem OpFun.id {C : Cat.{ℓobj ℓhom}}
    : OpFun (Fun.id C) = Fun.id ({{C}}⁻¹)
:= begin
     apply Fun.eq,
     { intro c, exact rfl },
     { intros x y f, apply heq.refl }
   end

/-! #brief OpFun distributes over functor composition.
-/
theorem OpFun.comp {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}} {E : Cat.{ℓobj₃ ℓhom₃}}
    {g : D ⇉⇉ E} {f : C ⇉⇉ D}
    : OpFun (g □□ f) = OpFun g □□ OpFun f
:= begin
     apply Fun.eq,
     { intro c, exact rfl },
     { intros x y f, apply heq.refl }
   end

/-! #brief The presheaf category.
-/
@[reducible] definition PreShCat (C : Cat.{ℓobj₁ ℓhom₁}) (D : Cat.{ℓobj₂ ℓhom₂})
    : Cat
:= FunCat {{C}}⁻¹ D



/- ----------------------------------------------------------------------------
Isomorphisms of categories.
---------------------------------------------------------------------------- -/

-- An isomorphism of categories.
structure CatIso {C₁ : Cat.{ℓobj₁ ℓhom₁}} {C₂ : Cat.{ℓobj₂ ℓhom₂}}
    (F₁₂ : C₁ ⇉⇉ C₂)
    (F₂₁ : C₂ ⇉⇉ C₁)
    : Prop
:= (id₁ : F₂₁ □□ F₁₂ = Fun.id C₁)
   (id₂ : F₁₂ □□ F₂₁ = Fun.id C₂)


/- ----------------------------------------------------------------------------
Natural isomorphisms.
---------------------------------------------------------------------------- -/

-- A natural isomorphism.
structure NatIso {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F₁ F₂ : C ⇉⇉ D}
    (η₁₂ : F₁ ↣↣ F₂)
    (η₂₁ : F₂ ↣↣ F₁)
    : Prop
:= (id₁ : η₂₁ ◇◇ η₁₂ = NatTrans.id F₁)
   (id₂ : η₁₂ ◇◇ η₂₁ = NatTrans.id F₂)



/- ----------------------------------------------------------------------------
Monomorphisms.
---------------------------------------------------------------------------- -/

-- A monomorphism.
definition IsMonic {C : Cat.{ℓobj ℓhom}}
    {x y : [[C]]}
    (f : x →→ y)
    : Prop
:= ∀ (a : [[C]]) (g₁ g₂ : a →→ x)
   , f ∘∘ g₁ = f ∘∘ g₂
   → g₁ = g₂



/- ----------------------------------------------------------------------------
Isomorphisms.
---------------------------------------------------------------------------- -/

-- An isomorphism in a category.
structure Iso {C : Cat.{ℓobj ℓhom}}
    {x₁ x₂ : [[C]]}
    (f₁₂ : x₁ →→ x₂)
    (f₂₁ : x₂ →→ x₁)
    : Prop
:= (id₁ : f₂₁ ∘∘ f₁₂ = ⟨⟨x₁⟩⟩)
   (id₂ : f₁₂ ∘∘ f₂₁ = ⟨⟨x₂⟩⟩)

-- Witness that a given hom is an isomorphism.
structure IsIso {C : Cat.{ℓobj ℓhom}}
    {x₁ x₂ : [[C]]}
    (f : x₁ →→ x₂)
    : Type (ℓhom + 1)
:= (inv : x₂ →→ x₁)
   (iso : Iso f inv)

/-! #brief Swap the hom's in an isomorphism.
-/
theorem Iso.swap {C : Cat.{ℓobj ℓhom}}
    {x₁ x₂ : [[C]]}
    {f₁₂ : x₁ →→ x₂}
    {f₂₁ : x₂ →→ x₁}
    (iso : Iso f₁₂ f₂₁)
    : Iso f₂₁ f₁₂
:= { id₁ := iso^.id₂
   , id₂ := iso^.id₁
   }

/-! #brief Iso coerces to IsIso (left edition).
-/
@[reducible] instance Iso.has_coe_IsIso_left {C : Cat.{ℓobj ℓhom}}
    {x₁ x₂ : [[C]]}
    {f₁₂ : x₁ →→ x₂}
    {f₂₁ : x₂ →→ x₁}
    : has_coe (Iso f₁₂ f₂₁) (IsIso f₁₂)
:= { coe := λ iso, { inv := f₂₁, iso := iso }
   }

/-! #brief Iso coerces to IsIso (right edition).
-/
@[reducible] instance Iso.has_coe_IsIso_right {C : Cat.{ℓobj ℓhom}}
    {x₁ x₂ : [[C]]}
    {f₁₂ : x₁ →→ x₂}
    {f₂₁ : x₂ →→ x₁}
    : has_coe (Iso f₁₂ f₂₁) (IsIso f₂₁)
:= { coe := λ iso, { inv := f₁₂, iso := Iso.swap iso }
   }

/-! #brief Identity homs are isomorphisms.
-/
theorem Iso.id {C : Cat.{ℓobj ℓhom}}
    (x : [[C]])
    : IsIso ⟨⟨x⟩⟩
:= { inv := ⟨⟨x⟩⟩
   , iso := { id₁ := C^.circ_id_left
            , id₂ := C^.circ_id_left
            }
   }

/-! #brief The composition of two isomorphisms is again an isomorphism.
-/
theorem Iso.circ {C : Cat.{ℓobj ℓhom}}
    {x₁ x₂ x₃ : [[C]]}
    {f₁₂ : x₁ →→ x₂} {f₂₁ : x₂ →→ x₁}
    {f₂₃ : x₂ →→ x₃} {f₃₂ : x₃ →→ x₂}
    (iso₁₂ : Iso f₁₂ f₂₁)
    (iso₂₃ : Iso f₂₃ f₃₂)
    : Iso (f₂₃ ∘∘ f₁₂) (f₂₁ ∘∘ f₃₂)
:= { id₁ := by calc (f₂₁ ∘∘ f₃₂) ∘∘ (f₂₃ ∘∘ f₁₂)
                        = f₂₁ ∘∘ ((f₃₂ ∘∘ f₂₃) ∘∘ f₁₂) : by simp [Cat.circ_assoc]
                    ... = f₂₁ ∘∘ (⟨⟨x₂⟩⟩ ∘∘ f₁₂)       : by rw iso₂₃^.id₁
                    ... = f₂₁ ∘∘ f₁₂                   : by simp
                    ... = ⟨⟨x₁⟩⟩                       : by rw iso₁₂^.id₁
   , id₂ := by calc (f₂₃ ∘∘ f₁₂) ∘∘ (f₂₁ ∘∘ f₃₂)
                        = f₂₃ ∘∘ ((f₁₂ ∘∘ f₂₁) ∘∘ f₃₂) : by simp [Cat.circ_assoc]
                    ... = f₂₃ ∘∘ (⟨⟨x₂⟩⟩ ∘∘ f₃₂)       : by rw iso₁₂^.id₂
                    ... = f₂₃ ∘∘ f₃₂                   : by simp
                    ... = ⟨⟨x₃⟩⟩                       : by rw iso₂₃^.id₂
   }

/-! #brief Isomorphisms are preserved by functors.
-/
theorem Fun.of_iso {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    (F : C ⇉⇉ D)
    {x₁ x₂ : [[C]]} {f : x₁ →→ x₂}
    (f_iso : IsIso f)
    : IsIso (F ↗ f)
:= { inv := F ↗ f_iso^.inv
   , iso := { id₁ := by rw [-F^.hom_circ, f_iso^.iso^.id₁, F^.hom_id]
            , id₂ := by rw [-F^.hom_circ, f_iso^.iso^.id₂, F^.hom_id]
            }
   }



/- ----------------------------------------------------------------------------
Initial and final objects.
---------------------------------------------------------------------------- -/

-- A final object.
structure Final (C : Cat.{ℓobj ℓhom})
    : Type (max ℓobj ℓhom)
:= (obj : [[C]])
   (hom : ∀ {x : [[C]]}, x →→ obj)
   (uniq : ∀ {x : [[C]]} (h : x →→ obj), h = hom)

/-! #brief Every final object can be treated as an objects.
-/
@[reducible] instance Final.has_coe_to_obj {C : Cat.{ℓobj ℓhom}}
    : has_coe (Final C) [[C]]
:= { coe := Final.obj
   }

/-! #brief Final objects are unique up to isomorphism.
-/
definition Final.Iso {C : Cat.{ℓobj ℓhom}}
    (x₁ x₂ : Final C)
    : Iso x₂^.hom x₁^.hom
:= { id₁ := begin dsimp, rw (x₁^.uniq ⟨⟨x₁^.obj⟩⟩), apply x₁^.uniq end
   , id₂ := begin dsimp, rw (x₂^.uniq ⟨⟨x₂^.obj⟩⟩), apply x₂^.uniq end
   }

/-! #brief Final objects are unique up to unique isomorphism.
-/
definition Final.Iso.uniq {C : Cat.{ℓobj ℓhom}}
    {x₁ x₂ : Final C}
    {f₁₂ : x₁^.obj →→ x₂^.obj} {f₂₁ : x₂^.obj →→ x₁^.obj}
    (f_iso : Iso f₁₂ f₂₁)
    : f₁₂ = x₂^.hom ∧ f₂₁ = x₁^.hom
:= and.intro (x₂^.uniq _) (x₁^.uniq _)


/-! #brief A category with a final object.
-/
class HasFinal (C : Cat.{ℓobj ℓhom})
    : Type (max ℓobj ℓhom)
:= (final : Final C)

/-! #brief The final object.
-/
definition final (C : Cat.{ℓobj ℓhom})
    [C_HasFinal : HasFinal C]
    : [[C]]
:= (HasFinal.final C)^.obj

/-! #brief The final hom.
-/
definition final_hom {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    {x : [[C]]}
    : x →→ final C
:= (HasFinal.final C)^.hom

/-! #brief The final hom is unique.
-/
@[simp] theorem final_hom.uniq {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    {x : [[C]]}
    (f : x →→ final C)
    : f = final_hom
:= by apply (HasFinal.final C)^.uniq

/-! #brief Final objects are unique up to isomorphism.
-/
theorem final.Iso {C : Cat.{ℓobj ℓhom}}
    (C_HasFinal₁ C_HasFinal₂ : HasFinal C)
    : Iso (@final_hom C C_HasFinal₁ _)
          (@final_hom C C_HasFinal₂ _)
:= Final.Iso _ _


/-! #brief An initial object.
-/
definition Init (C : Cat.{ℓobj ℓhom})
    : Type (max ℓobj ℓhom)
:= Final {{C}}⁻¹

/-! #brief Every initial object can be treated as an objects.
-/
@[reducible] instance Init.has_coe_to_obj {C : Cat.{ℓobj ℓhom}}
    : has_coe (Init C) [[C]]
:= Final.has_coe_to_obj

/-! #brief Initial objects are unique up to isomorphism.
-/
definition Init.Iso {C : Cat.{ℓobj ℓhom}}
    (x₁ x₂ : Init C)
    : Iso x₂^.hom x₁^.hom
:= Final.Iso x₁ x₂


/-! #brief A category with an initial object.
-/
class HasInit (C : Cat.{ℓobj ℓhom})
    : Type (max ℓobj ℓhom)
:= (init : Init C)

/-! #brief The initial object.
-/
definition init (C : Cat.{ℓobj ℓhom})
    [C_HasInit : HasInit C]
    : [[C]]
:= by apply (HasInit.init C)^.obj

/-! #brief The initial hom.
-/
definition init_hom {C : Cat.{ℓobj ℓhom}}
    [C_HasInit : HasInit C]
    {x : [[C]]}
    : init C →→ x
:= (HasInit.init C)^.hom

/-! #brief The initial hom is unique.
-/
@[simp] theorem init_hom.uniq {C : Cat.{ℓobj ℓhom}}
    [C_HasInit : HasInit C]
    {x : [[C]]}
    (f : init C →→ x)
    : f = init_hom
:= by apply (HasInit.init C)^.uniq

/-! #brief Initial objects are unique up to isomorphism.
-/
theorem init.Iso {C : Cat.{ℓobj ℓhom}}
    (C_HasInit₁ C_HasInit₂ : HasInit C)
    : Iso (@init_hom C C_HasInit₁ _)
          (@init_hom C C_HasInit₂ _)
:= { id₁ := begin unfold init_hom, apply (Init.Iso _ _)^.id₁ end
   , id₂ := begin unfold init_hom, apply (Init.Iso _ _)^.id₁ end
   }



/- ----------------------------------------------------------------------------
Adjoint functors.
---------------------------------------------------------------------------- -/

-- An adjunction between two functors.
structure Adj
    {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    (L : C ⇉⇉ D)
    (R : D ⇉⇉ C)
  : Type (max ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂)
  := mk :: (counit : L □□ R ↣↣ Fun.id D)
           (unit : Fun.id C ↣↣ R □□ L)
           (id_left : ∀ {c : [[C]]}, counit (L c) ∘∘ L^.hom (unit c) = ⟨⟨L c⟩⟩)
           (id_right : ∀ {d : [[D]]}, R^.hom (counit d) ∘∘ unit (R d) = ⟨⟨R d⟩⟩)

attribute [simp] Adj.id_left
attribute [simp] Adj.id_right

-- An adjunction of functors.
-- \dashv
notation L `⊣` R := Adj L R

/-! #brief The right adjoint of a hom.
-/
@[reducible] definition Adj.right_adj {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {L : C ⇉⇉ D} {R : D ⇉⇉ C} (adj : L ⊣ R)
    {c : [[C]]} {d : [[D]]}   (f : L c →→ d)
    : c →→ R d
:= (R ↗ f) ∘∘ adj^.unit c

/-! #brief The left adjoint of a hom.
-/
@[reducible] definition Adj.left_adj {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {L : C ⇉⇉ D} {R : D ⇉⇉ C} (adj : L ⊣ R)
    {c : [[C]]} {d : [[D]]}   (f : c →→ R d)
    : L c →→ d
:= adj^.counit d ∘∘ (L ↗ f)

/-! #brief right_adj and left_adj are inverses of one another.
-/
@[simp] theorem Adj.right_adj_left_adj {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {L : C ⇉⇉ D} {R : D ⇉⇉ C} {adj : L ⊣ R}
    {c : [[C]]} {d : [[D]]}   {f : c →→ R d}
    : Adj.right_adj adj (Adj.left_adj adj f) = f
:= let foo := adj^.unit in
   begin
     unfold Adj.right_adj,
     unfold Adj.left_adj,
     calc (R ↗ adj^.counit d ∘∘ (L ↗ f)) ∘∘ adj^.unit c
              = ((R ↗ adj^.counit d) ∘∘ (R ↗ (L ↗ f))) ∘∘ adj^.unit c : by rw R^.hom_circ
          ... = (R ↗ adj^.counit d) ∘∘ ((R ↗ (L ↗ f))) ∘∘ adj^.unit c : by rw -C^.circ_assoc
          ... = (R ↗ adj^.counit d) ∘∘ (adj^.unit (R d) ∘∘ f)         : sorry -- by rw -adj^.unit^.transport
          ... = ((R ↗ adj^.counit d) ∘∘ adj^.unit (R d)) ∘∘ f         : by rw C^.circ_assoc
          ... = ⟨⟨R d⟩⟩ ∘∘ f                                          : begin rw adj^.id_right, apply rfl end
          ... = f                                                     : C^.circ_id_left
   end

/-! #brief left_adj and right_adj are inverses of one another.
-/
@[simp] theorem Adj.left_adj_right_adj {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {L : C ⇉⇉ D} {R : D ⇉⇉ C} {adj : L ⊣ R}
    {c : [[C]]} {d : [[D]]}   {f : L c →→ d}
    : Adj.left_adj adj (Adj.right_adj adj f) = f
:= begin
     unfold Adj.right_adj,
     unfold Adj.left_adj,
     calc adj^.counit d ∘∘ (L ↗ ((R ↗ f) ∘∘ adj^.unit c))
              = adj^.counit d ∘∘ ((L ↗ (R ↗ f)) ∘∘ (L ↗ (adj^.unit c))) : begin rw L^.hom_circ, apply rfl end
          ... = (adj^.counit d ∘∘ (L ↗ (R ↗ f))) ∘∘ (L ↗ (adj^.unit c)) : by rw D^.circ_assoc
          ... = f ∘∘ adj^.counit (L c) ∘∘ (L ↗ (adj^.unit c))           : sorry -- by rw adj^.counit^.transport
          ... = f ∘∘ (adj^.counit (L c) ∘∘ (L ↗ (adj^.unit c)))         : by rw -D^.circ_assoc
          ... = f ∘∘ ⟨⟨L c⟩⟩                                            : begin rw -adj^.id_left, apply rfl end
          ... = f                                                       : D^.circ_id_right
   end



/- ----------------------------------------------------------------------------
Product categories.
---------------------------------------------------------------------------- -/

/-! #brief The product category.
-/
@[reducible] definition ProdCat (C : Cat.{ℓobj₁ ℓhom₁}) (D : Cat.{ℓobj₂ ℓhom₂})
    : Cat.{(max ℓobj₁ ℓobj₂) (max 1 ℓhom₁ ℓhom₂)}
:= { obj := pprod [[C]] [[D]]
   , hom := λ x y, pprod (x^.fst →→ y^.fst) (x^.snd →→ y^.snd)
   , id  := λ x, pprod.mk ⟨⟨x^.fst⟩⟩ ⟨⟨x^.snd⟩⟩
   , circ := λ x y z g f, pprod.mk (g^.fst ∘∘ f^.fst) (g^.snd ∘∘ f^.snd)
   , circ_assoc
      := λ x y z w h g f
         , begin dsimp, rw [C^.circ_assoc, D^.circ_assoc] end
   , circ_id_left := λ x y f, begin dsimp, simp, cases f , apply rfl end
   , circ_id_right := λ x y f, begin dsimp, simp, cases f , apply rfl end
   }

-- The product category.
-- \times\times
infixr `××` : 130 := ProdCat

/-! #brief Left-projection functor from the ProdCat.
-/
definition ProdCat.π₁Fun {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    : C ×× D ⇉⇉ C
:= { obj := λ x, x^.fst
   , hom := λ x y f, f^.fst
   , hom_id := λ x, rfl
   , hom_circ := λ x y z g f, rfl
   }

@[simp] theorem ProdCat.π₁Fun.simp_obj {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    (cd : [[C ×× D]])
    : @ProdCat.π₁Fun C D cd = cd^.fst
:= rfl

@[simp] theorem ProdCat.π₁Fun.simp_hom {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {cd₁ cd₂ : [[C ×× D]]} (f : (C ×× D)^.hom cd₁ cd₂)
    : @ProdCat.π₁Fun C D ↗ f = f^.fst
:= rfl

/-! #brief Right-projection functor from the ProdCat.
-/
definition ProdCat.π₂Fun {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    : C ×× D ⇉⇉ D
:= { obj := λ x, x^.snd
   , hom := λ x y f, f^.snd
   , hom_id := λ x, rfl
   , hom_circ := λ x y z g f, rfl
   }

@[simp] theorem ProdCat.π₂Fun.simp_obj {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    (cd : [[C ×× D]])
    : @ProdCat.π₂Fun C D cd = cd^.snd
:= rfl

@[simp] theorem ProdCat.π₂Fun.simp_hom {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {cd₁ cd₂ : [[C ×× D]]} (f : (C ×× D)^.hom cd₁ cd₂)
    : @ProdCat.π₂Fun C D ↗ f = f^.snd
:= rfl

/-! #brief Flip the factors in ProdCat.
-/
definition ProdCat.flip {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    : C ×× D ⇉⇉ D ×× C
:= { obj := λ x, { fst := x^.snd, snd := x^.fst }
   , hom := λ x y f, { fst := f^.snd, snd := f^.fst }
   , hom_id := λ x, rfl
   , hom_circ := λ x y z g f, rfl
   }

@[simp] theorem ProdCat.flip.simp_obj {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    (cd : [[C ×× D]])
    : @ProdCat.flip C D cd = { fst := cd^.snd, snd := cd^.fst }
:= rfl

@[simp] theorem ProdCat.flip.simp_hom {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {cd₁ cd₂ : [[C ×× D]]} (f : (C ×× D)^.hom cd₁ cd₂)
    : @ProdCat.flip C D ↗ f = { fst := f^.snd, snd := f^.fst }
:= rfl

/-! #brief Flip is involutive.
-/
@[simp] theorem ProdCat.flip_flip {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    : ProdCat.flip □□ ProdCat.flip = Fun.id (C ×× D)
:= begin
     apply Fun.eq,
     { intro x, cases x with c d, apply rfl },
     { intros x y f,
       cases x with c₁ d₁, cases y with c₂ d₂, cases f with fc fd,
       apply heq.refl
     }
   end

/-! #brief Flip the arguments of a natural transformation.
-/
definition NatTrans.flip 
    {C₁ : Cat.{ℓobj₁ ℓhom₁}} {C₂ : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    {F₁ : C₁ ×× C₂ ⇉⇉ D} {F₂ : C₂ ×× C₁ ⇉⇉ D}
    (η : F₁ ↣↣ F₂ □□ ProdCat.flip)
    : F₁ □□ ProdCat.flip ↣↣ F₂
:= { component := λ c, pprod.cases_on c (λ c₂ c₁, η ⟨c₁, c₂⟩)
   , transport
      := λ x y f
         , begin
             cases x with x₂ x₁,
             cases y with y₂ y₁,
             cases f with f₂ f₁,
             exact @NatTrans.transport _ _ _ _ η ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ ⟨f₁, f₂⟩
           end
   }

@[simp] theorem NatTrans.flip.simp_component
    {C₁ : Cat.{ℓobj₁ ℓhom₁}} {C₂ : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    {F₁ : C₁ ×× C₂ ⇉⇉ D} {F₂ : C₂ ×× C₁ ⇉⇉ D}
    (η : F₁ ↣↣ F₂ □□ ProdCat.flip)
    (x : [[C₂ ×× C₁]])
    : NatTrans.flip η x = pprod.cases_on x (λ c₂ c₁, η ⟨c₁, c₂⟩)
:= rfl

/-! #brief Un-flip the arguments of a natural transformation.
-/
definition NatTrans.unflip 
    {C₁ : Cat.{ℓobj₁ ℓhom₁}} {C₂ : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    {F₁ : C₁ ×× C₂ ⇉⇉ D} {F₂ : C₂ ×× C₁ ⇉⇉ D}
    (η : F₁ □□ ProdCat.flip ↣↣ F₂)
    : F₁ ↣↣ F₂ □□ ProdCat.flip
:= { component := λ c, pprod.cases_on c (λ c₁ c₂, η ⟨c₂, c₁⟩)
   , transport
      := λ x y f
         , begin
             cases x with x₁ x₂,
             cases y with y₁ y₂,
             cases f with f₁ f₂,
             exact @NatTrans.transport _ _ _ _ η ⟨x₂, x₁⟩ ⟨y₂, y₁⟩ ⟨f₂, f₁⟩
           end
   }

@[simp] theorem NatTrans.unflip.simp_component
    {C₁ : Cat.{ℓobj₁ ℓhom₁}} {C₂ : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    {F₁ : C₁ ×× C₂ ⇉⇉ D} {F₂ : C₂ ×× C₁ ⇉⇉ D}
    (η : F₁ □□ ProdCat.flip ↣↣ F₂)
    (x : [[C₁ ×× C₂]])
    : NatTrans.unflip η x = pprod.cases_on x (λ c₁ c₂, η ⟨c₂, c₁⟩)
:= rfl

/-! #brief Left-associate ProdCat.
-/
definition ProdCat.assoc_left {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}} {E : Cat.{ℓobj₃ ℓhom₃}}
    : C ×× (D ×× E) ⇉⇉ (C ×× D) ×× E
:= { obj := λ x, { fst := { fst := x^.fst, snd := x^.snd^.fst }, snd := x^.snd^.snd }
   , hom := λ x y f, { fst := { fst := f^.fst, snd := f^.snd^.fst }, snd := f^.snd^.snd }
   , hom_id := λ x, rfl
   , hom_circ := λ x y z g f, rfl
   }

@[simp] theorem ProdCat.assoc_left.simp_obj {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}} {E : Cat.{ℓobj₃ ℓhom₃}}
    (x : [[C ×× (D ×× E)]])
    : @ProdCat.assoc_left C D E x = { fst := { fst := x^.fst, snd := x^.snd^.fst }, snd := x^.snd^.snd }
:= rfl

@[simp] theorem ProdCat.assoc_left.simp_hom {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}} {E : Cat.{ℓobj₃ ℓhom₃}}
    {x₁ x₂ : [[C ×× (D ×× E)]]} (f : (C ×× (D ×× E))^.hom x₁ x₂)
    : @ProdCat.assoc_left C D E ↗ f = { fst := { fst := f^.fst, snd := f^.snd^.fst }, snd := f^.snd^.snd }
:= rfl

/-! #brief Right-associate ProdCat.
-/
definition ProdCat.assoc_right {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}} {E : Cat.{ℓobj₃ ℓhom₃}}
    : (C ×× D) ×× E ⇉⇉ C ×× (D ×× E)
:= { obj := λ x, { fst := x^.fst^.fst, snd := { fst := x^.fst^.snd, snd := x^.snd } }
   , hom := λ x y f, { fst := f^.fst^.fst, snd := { fst := f^.fst^.snd, snd := f^.snd } }
   , hom_id := λ x, rfl
   , hom_circ := λ x y z g f, rfl
   }

@[simp] theorem ProdCat.assoc_right.simp_obj {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}} {E : Cat.{ℓobj₃ ℓhom₃}}
    (x : [[(C ×× D) ×× E]])
    : @ProdCat.assoc_right C D E x = { fst := x^.fst^.fst, snd := { fst := x^.fst^.snd, snd := x^.snd } }
:= rfl

@[simp] theorem ProdCat.assoc_right.simp_hom {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}} {E : Cat.{ℓobj₃ ℓhom₃}}
    {x₁ x₂ : [[(C ×× D) ×× E]]} (f : ((C ×× D) ×× E)^.hom x₁ x₂)
    : @ProdCat.assoc_right C D E ↗ f = { fst := f^.fst^.fst, snd := { fst := f^.fst^.snd, snd := f^.snd } }
:= rfl



/- ----------------------------------------------------------------------------
SortCat, PropCat, and LeanCat.
---------------------------------------------------------------------------- -/

/-! #brief The category of Sort terms in Sort ℓ and functions between them.
-/
@[reducible] definition SortCat : Cat.{ℓ ℓ}
:= { obj := Sort.{ℓ}
   , hom := λ X Y, X → Y
   , id := λ X x, x
   , circ := λ X Y Z g f x, g (f x)
   , circ_assoc := λ X Y Z W h g f, rfl
   , circ_id_left := λ X Y f, rfl
   , circ_id_right := λ X Y f, rfl
   }

/-! #brief The category of propositions and implications between them.
-/
@[reducible] definition PropCat : Cat.{0 0} := SortCat.{0}

/-! #brief The category of types and functions between them.
-/
@[reducible] definition LeanCat : Cat.{(ℓ + 1) (ℓ + 1)} := SortCat.{ℓ + 1}

/-! #brief pempty is an initial object in LeanCat.
-/
@[reducible] definition LeanCat.Init
    : Init LeanCat.{ℓ}
:= { obj := pempty.{ℓ + 1}
   , hom := λ A, pempty.elim
   , uniq := λ A f, begin
                      apply pfunext, intro e,
                      exact pempty.elim e
                    end
   }

/-! #brief punit is a final object in LeanCat.
-/
@[reducible] definition LeanCat.Final
    : Final LeanCat.{ℓ}
:= { obj := punit.{ℓ + 1}
   , hom := λ A a, punit.star
   , uniq := λ A f, begin
                      apply pfunext, intro a,
                      apply punit.uniq
                    end
   }

/-! #brief The category of Lean terms in finite types.
-/
@[reducible] definition FinLeanCat : Cat.{(ℓ + 1) (ℓ + 1)}
:= { obj := BxFinType.{ℓ}
   , hom := λ X Y, X^.T → Y^.T
   , id := λ X x, x
   , circ := λ X Y Z g f x, g (f x)
   , circ_assoc := λ X Y Z W h g f, rfl
   , circ_id_left := λ X Y f, rfl
   , circ_id_right := λ X Y f, rfl
   }

/-! #brief The functor from CatCat to LeanCat.
-/
definition CatCat.toLean
    : CatCat.{ℓobj ℓhom} ⇉⇉ LeanCat.{ℓobj}
:= { obj := λ C, [[C]]
   , hom := λ C D F x, F x
   , hom_id := λ C, rfl
   , hom_circ := λ B C D G F, rfl
   }

@[simp] theorem CatCat.toLean.simp_obj
    (C : [[CatCat.{ℓobj ℓhom}]])
    : CatCat.toLean C = [[C]]
:= rfl

@[simp] theorem CatCat.toLean.simp_hom
    {C₁ C₂ : [[CatCat.{ℓobj ℓhom}]]} (F : (CatCat.{ℓobj ℓhom})^.hom C₁ C₂)
    : CatCat.toLean ↗ F = F^.obj
:= rfl

/-! #brief The Hom functor to LeanCat.
-/
definition HomFun (C : Cat.{ℓobj ℓhom})
    : {{C}}⁻¹ ×× C ⇉⇉ SortCat.{ℓhom}
:= { obj := λ x, x^.fst →→ x^.snd
   , hom := λ x y fg c, fg^.snd ∘∘ c ∘∘ fg^.fst
   , hom_id := λ x, begin apply pfunext, intro f, simp, simp end
   , hom_circ
       := λ x y z g f
          , begin
              simp,
              apply pfunext, intro c,
              dsimp, simp [Cat.circ_assoc]
            end
   }

@[simp] theorem HomFun.simp_obj {C : Cat.{ℓobj ℓhom}}
    (c : [[{{C}}⁻¹ ×× C]])
    : HomFun C c = c^.fst →→ c^.snd
:= rfl

@[simp] theorem HomFun.simp_hom {C : Cat.{ℓobj ℓhom}}
    {c₁ c₂ : [[{{C}}⁻¹ ×× C]]} (f : ({{C}}⁻¹ ×× C)^.hom c₁ c₂)
    : HomFun C ↗ f = λ m, f^.snd ∘∘ m ∘∘ f^.fst
:= rfl



/- ----------------------------------------------------------------------------
Categories with no nontrivial homs.
---------------------------------------------------------------------------- -/

/-! #brief Homs in ObjCat.
-/
inductive ObjCatHom (A : Type ℓ) : A → A → Type ℓ
| id : ∀ (a : A), ObjCatHom a a

/-! #brief Composition in ObjCat.
-/
definition ObjCatHom.comp {A : Type ℓ}
    : ∀ {x y z : A}
        (g : ObjCatHom A y z)
        (f : ObjCatHom A x y)
      , ObjCatHom A x z
| x .x y g (ObjCatHom.id .x) := g

/-! #brief ObjCatHom.id is a left identity for ObjCat.Hom.comp.
-/
@[simp] theorem ObjCatHom.comp_id_left {A : Type ℓ}
    : ∀ {x y : A}
        {f : ObjCatHom A x y}
      , ObjCatHom.comp (ObjCatHom.id y) f = f
| x .x (ObjCatHom.id .x) := rfl

/-! #brief ObjCatHom.id is a right identity for ObjCat.Hom.comp.
-/
@[simp] theorem ObjCatHom.comp_id_right {A : Type ℓ}
    : ∀ {x y : A}
        {f : ObjCatHom A x y}
      , ObjCatHom.comp f (ObjCatHom.id x) = f
| x .x (ObjCatHom.id .x) := rfl

/-! #brief A category with no nontrivial homs.
-/
@[reducible] definition ObjCat (A : Type ℓ) : Cat.{ℓ (ℓ + 1)}
:= { obj := A
   , hom := ObjCatHom A
   , id := ObjCatHom.id
   , circ := λ x y z g f, ObjCatHom.comp g f
   , circ_assoc := λ x y z w h g f, begin cases f, cases g, apply rfl end
   , circ_id_left := λ x y f, by simp
   , circ_id_right := λ x y f, by simp
   }

/-! #brief ObjCat has no nontrivial homs.
-/
theorem ObjCat.hom_trivial {A : Type ℓ}
    : ∀ {x y : [[ObjCat A]]}
        (f : (ObjCat A)^.hom x y)
      , x = y
| x .x (ObjCatHom.id .x) := rfl

/-! #brief ObjCat A is finite when A is.
-/
instance ObjCat.Fin {A : Type ℓ}
    (A_FinType : FinType A)
    : Cat.Fin (ObjCat A)
:= { obj := A_FinType
   , hom
      := λ x y
         , if ωnxy : A_FinType^.n_of x = A_FinType^.n_of y
            then { card := 1
                 , of_n
                    := λ n
                       , begin
                           rw function.injective_of_left_inverse A_FinType^.of_n_of ωnxy,
                           apply ObjCatHom.id
                         end
                 , n_of := λ n, { val := 0, is_lt := by apply nat.less_than_or_equal.refl }
                 , n_of_n := λ n, eq.symm fin.one
                 , of_n_of
                    := λ n
                       , begin
                           assert ωxy : x = y,
                           { rw function.injective_of_left_inverse A_FinType^.of_n_of ωnxy },
                           subst ωxy,
                           cases n,
                           apply rfl
                         end
                 }
            else { card := 0
                 , of_n := λ n, fin.zero_elim n
                 , n_of
                    := λ n
                       , begin
                           assert ω : false,
                           { apply ωnxy, rw ObjCat.hom_trivial n },
                           cases ω
                         end
                 , n_of_n := λ n, fin.zero_elim n
                 , of_n_of
                    := λ n
                       , begin
                           assert ω : false,
                           { apply ωnxy, rw ObjCat.hom_trivial n },
                           cases ω
                         end
                 }
   }



/- ----------------------------------------------------------------------------
The empty category.
---------------------------------------------------------------------------- -/

/-! #brief The category with no objects.
-/
definition EmptyCat
    : Cat.{ℓobj ℓhom}
:= { obj := pempty.{ℓobj + 1}
   , hom := λ x y, pempty.{ℓhom}
   , id := λ x, pempty.elim x
   , circ := λ x y z g f, f
   , circ_assoc := λ x y z w h g f, rfl
   , circ_id_left := λ x y f, rfl
   , circ_id_right := λ x y f, begin cases x end
   }

/-! #brief EmptyCat is finite.
-/
@[reducible] instance EmptyCat.Fin : Cat.Fin EmptyCat.{ℓobj ℓhom}
:= { obj := pempty.FinType
   , hom := λ x y, pempty.FinType
   }

/-! #brief The functor from EmptyCat to an arbitrary category.
-/
@[reducible] definition EmptyCat.init (C : Cat.{ℓobj₁ ℓhom₁})
    : EmptyCat.{ℓobj₂ ℓhom₂} ⇉⇉ C
:= { obj := λ e, begin cases e end
   , hom := λ x y f, begin cases f end
   , hom_id := λ x, begin cases x end
   , hom_circ := λ x y z g f, begin cases f end
   }

/-! #brief EmptyCat is initial in CatCat.
-/
definition CatCat.Init
    : Init CatCat.{ℓobj ℓhom}
:= { obj := EmptyCat.{ℓobj ℓhom}
   , hom := EmptyCat.init
   , uniq
      := λ C F
         , begin
             apply Fun.eq,
             { intro x, cases x },
             { intros x y f, cases f }
           end
   }



/- ----------------------------------------------------------------------------
The category with one object.
---------------------------------------------------------------------------- -/

/-! #brief The category with one object.
-/
@[reducible] definition StarCat
    : Cat.{ℓobj ℓhom}
:= { obj := punit.{ℓobj + 1}
   , hom := λ x y, punit.{ℓhom}
   , id := λ x, punit.star
   , circ := λ x y z g f, f
   , circ_assoc := λ x y z w h g f, rfl
   , circ_id_left := λ x y f, rfl
   , circ_id_right := λ x y f, begin cases f, apply rfl end
   }

/-! #brief StarCat is finite.
-/
@[reducible] instance StarCat.Fin : Cat.Fin StarCat.{ℓobj ℓhom}
:= { obj := punit.FinType
   , hom := λ x y, punit.FinType
   }

/-! #brief The functor from an arbitrary category to StarCat.
-/
@[reducible] definition StarCat.final (C : Cat.{ℓobj₁ ℓhom₁})
    : C ⇉⇉ StarCat.{ℓobj₂ ℓhom₂}
:= { obj := λ c, punit.star
   , hom := λ x y f, punit.star
   , hom_id := λ x, rfl
   , hom_circ := λ x y z g f, rfl
   }

/-! #brief StarCat is final in CatCat.
-/
@[reducible] definition CatCat.Final
    : Final CatCat.{ℓobj ℓhom}
:= { obj := StarCat.{ℓobj ℓhom}
   , hom := StarCat.final
   , uniq
      := λ C F
         , begin
             apply Fun.eq,
             { intro x, apply punit.uniq },
             { intros x y f,
               apply heq_of_eq,
               exact eq.trans punit.uniq (eq.symm punit.uniq)
             }
           end
   }



/- ----------------------------------------------------------------------------
Slice categories.
---------------------------------------------------------------------------- -/

-- An object in a slice category.
structure SliceObj (C : Cat.{ℓobj ℓhom}) (c : [[C]])
    : Type (max ℓobj ℓhom)
:= (dom : [[C]])
   (hom : dom →→ c)

-- A hom in a slice category.
structure SliceHom {C : Cat.{ℓobj ℓhom}} {c : [[C]]}
    (x y : SliceObj C c)
    : Type ℓhom
:= (hom : C^.hom x^.dom y^.dom)
   (triangle : x^.hom = y^.hom ∘∘ hom)

/-! #brief Helper for proving equality of slice category homs.
-/
theorem SliceHom.eq {C : Cat.{ℓobj ℓhom}} {c : [[C]]}
    {x y : SliceObj C c}
    : ∀ {f₁ f₂ : SliceHom x y}
      , f₁^.hom = f₂^.hom
      → f₁ = f₂
| (SliceHom.mk f ω₁) (SliceHom.mk .f ω₂) (eq.refl .f) := rfl

/-! #brief The identity hom in a slice category.
-/
definition SliceHom.id {C : Cat.{ℓobj ℓhom}} {c : [[C]]}
    (x : SliceObj C c)
    : SliceHom x x
:= { hom := ⟨⟨x^.dom⟩⟩
   , triangle := by simp
   }

@[simp] theorem SliceHom.id.simp_hom {C : Cat.{ℓobj ℓhom}} {c : [[C]]}
    (x : SliceObj C c)
    : (SliceHom.id x)^.hom = ⟨⟨x^.dom⟩⟩
:= rfl

/-! #brief Composition of homs in a slice category.
-/
definition SliceHom.comp {C : Cat.{ℓobj ℓhom}} {c : [[C]]}
    {x y z : SliceObj C c} (g : SliceHom y z) (f : SliceHom x y)
    : SliceHom x z
:= { hom := g^.hom ∘∘ f^.hom
   , triangle := by rw [f^.triangle, g^.triangle, C^.circ_assoc]
   }

@[simp] theorem SliceHom.comp.simp_hom {C : Cat.{ℓobj ℓhom}} {c : [[C]]}
    {x y z : SliceObj C c} (g : SliceHom y z) (f : SliceHom x y)
    : (SliceHom.comp g f)^.hom = g^.hom ∘∘ f^.hom
:= rfl

/-! #brief Slice categories.
-/
@[reducible] definition SliceCat
    (C : Cat.{ℓobj ℓhom})
    (c : [[C]])
    : Cat.{(max ℓobj ℓhom) (ℓhom + 1)}
:= { obj := SliceObj C c
   , hom := SliceHom
   , id := SliceHom.id
   , circ := @SliceHom.comp C c
   , circ_assoc := λ x y z w h g f, begin apply SliceHom.eq, dsimp, rw C^.circ_assoc end
   , circ_id_left := λ x y f, begin apply SliceHom.eq, dsimp, simp end
   , circ_id_right := λ x y f, begin apply SliceHom.eq, dsimp, simp end
   }

/-! #brief Every slice category has a final object.
-/
instance SliceCat.HasFinal {C : Cat.{ℓobj ℓhom}} {c : [[C]]}
    : HasFinal (SliceCat C c)
:= { final
      := { obj := { dom := c, hom := ⟨⟨c⟩⟩ }
         , hom := λ x, { hom := x^.hom
                       , triangle := by simp
                       }
         , uniq := λ x h
                   , begin
                       apply SliceHom.eq,
                       apply eq.symm,
                       apply eq.trans h^.triangle,
                       simp
                     end
         }
   }

/-! #brief Every hom induces a functor between slice categories.
-/
definition SliceFun {C : Cat.{ℓobj ℓhom}}
    {X Y : [[C]]} (f : X →→ Y)
    : SliceCat C X ⇉⇉ SliceCat C Y
:= { obj := λ x, { dom := x^.dom
                 , hom := f ∘∘ x^.hom
                 }
   , hom := λ x y f, { hom := f^.hom
                     , triangle := begin dsimp, rw [f^.triangle, C^.circ_assoc] end
                     }
   , hom_id := λ x, begin apply SliceHom.eq, apply rfl end
   , hom_circ := λ x y z g f, begin apply SliceHom.eq, apply rfl end
   }

@[simp] theorem SliceFun.simp_obj_dom {C : Cat.{ℓobj ℓhom}}
    {X Y : [[C]]} (f : X →→ Y) (x : [[SliceCat C X]])
    : ((SliceFun f) x)^.dom = x^.dom
:= rfl

@[simp] theorem SliceFun.simp_obj_hom {C : Cat.{ℓobj ℓhom}}
    {X Y : [[C]]} (f : X →→ Y) (x : [[SliceCat C X]])
    : ((SliceFun f) x)^.hom = f ∘∘ x^.hom
:= rfl

@[simp] theorem SliceFun.simp_hom_hom {C : Cat.{ℓobj ℓhom}}
    {X Y : [[C]]} (f : X →→ Y) {x₁ x₂ : [[SliceCat C X]]} (g : (SliceCat C X)^.hom x₁ x₂)
    : ((SliceFun f) ↗ g)^.hom = g^.hom
:= rfl

/-! #brief The category slicing functor.
-/
definition SliceCatFun (C : Cat.{ℓobj ℓhom})
    : C ⇉⇉ CatCat
:= { obj := λ c, SliceCat C c
   , hom := λ x y f, SliceFun f
   , hom_id := λ x, begin
                      apply Fun.eq,
                      { intro x₀, rw [Fun.id.simp_obj], cases x₀, apply congr_arg (SliceObj.mk dom), simp },
                      { intros x₀ x₁ f, dsimp, cases f, exact sorry }
                    end
   , hom_circ := λ x y z g f
                 , begin
                     apply Fun.eq,
                     { intro x₀, cases x₀, apply congr_arg (SliceObj.mk dom), rw [-C^.circ_assoc], apply rfl },
                     { intros x₀ x₁ f, dsimp, cases f, exact sorry }
                   end
   }

/-! #brief The functor from the slice category to the global category.
-/
definition UnsliceFun {C : Cat.{ℓobj ℓhom}} {c : [[C]]}
    : SliceCat C c ⇉⇉ C
:= { obj := λ x, x^.dom
   , hom := λ x y f, f^.hom
   , hom_id := λ x, rfl
   , hom_circ := λ x y z g f, rfl
   }

@[simp] theorem UnsliceFun.simp_obj {C : Cat.{ℓobj ℓhom}} {c : [[C]]}
    (x : [[SliceCat C c]])
    : @UnsliceFun C c x = x^.dom
:= rfl

@[simp] theorem UnsliceFun.simp_hom {C : Cat.{ℓobj ℓhom}} {c : [[C]]}
    {x₁ x₂ : [[SliceCat C c]]} (f : (SliceCat C c)^.hom x₁ x₂)
    : @UnsliceFun C c ↗ f = f^.hom
:= rfl

/-! #brief SliceCat C final is iso to C.
-/
@[reducible] definition SliceFinalFun (C : Cat.{ℓobj ℓhom})
    [C_HasFinal : HasFinal C]
    : C ⇉⇉ SliceCat C (final C)
:= { obj := λ c, { dom := c, hom := final_hom }
   , hom := λ c₁ c₂ f, { hom := f
                       , triangle := eq.symm (final_hom.uniq _)
                       }
   , hom_id := λ c, begin apply SliceHom.eq, apply rfl end
   , hom_circ := λ c₁ c₂ c₃ g f, begin apply SliceHom.eq, apply rfl end
   }

/-! #brief UnsliceFun and SliceFinalFun form an isomorphism.
-/
definition Unslice_SliceFinal.Iso {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    : CatIso UnsliceFun (SliceFinalFun C)
:= { id₁ := begin
              apply Fun.eq,
              { intro X, cases X, apply congr_arg (SliceObj.mk dom), exact eq.symm (final_hom.uniq _) },
              { intros X Y f, cases f with f ωXhom, dsimp, exact sorry }
            end
   , id₂ := begin
              apply Fun.eq,
              { intro X, apply rfl },
              { intros X Y f, apply heq.refl }
            end
   }



/- ----------------------------------------------------------------------------
The category of natural numbers.
---------------------------------------------------------------------------- -/

definition NatCat : Cat
:= { obj := ℕ
   , hom := λ x y, { m : ℕ // y = m + x }
   , id := λ x, { elt_of := 0, has_property := by simp }
   , circ := λ x y z g f, { elt_of := f^.elt_of + g^.elt_of
                          , has_property
                             := begin
                                  cases g with g ωg, apply eq.trans ωg,
                                  cases f with f ωf, apply eq.trans (congr_arg (λ f', g + f') ωf),
                                  simp
                                end
                          }
   , circ_assoc := λ x y z w h g f, begin apply subtype.eq, simp end
   , circ_id_left := λ x y f, begin apply subtype.eq, simp end
   , circ_id_right := λ x y f, begin apply subtype.eq, simp end
   }

-- @[reducible] definition NatCat : Cat
-- := { obj := ℕ
--    , hom := λ x y, x ≤ y
--    , id := nat.le_refl
--    , circ := λ x y z g f, by calc x   ≤ y : f
--                                   ... ≤ z : g
--    , circ_assoc := λ x y z w h g f, rfl
--    , circ_id_left := λ x y f, by apply proof_irrel
--    , circ_id_right := λ x y f, by apply proof_irrel
--    }

end qp
