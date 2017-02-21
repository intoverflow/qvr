/- ----------------------------------------------------------------------------
The basic definitions of category theory, together with the most fundamental
properties.
---------------------------------------------------------------------------- -/

import ..util

namespace qp
universe variables ℓobj ℓhom ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂ ℓobj₃ ℓhom₃ ℓobj₄ ℓhom₄



/- ----------------------------------------------------------------------------
The three main notions in category theory are here defined: Cat, Fun, and
NatTrans.
---------------------------------------------------------------------------- -/

-- A strict category.
structure Cat : Type (max ℓobj ℓhom)
:= (obj : Sort ℓobj)
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

/-! #brief Every functor can be treated as a function on homs.
-/
/-
instance Fun.hom_has_coe_to_fun {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    : has_coe_to_fun (C ⇉⇉ D)
:= { F := λ G, ∀ {x y : [[C]]} (f : x →→ y), G x →→ G y
   , coe := λ G x y f, G^.hom f
   }
-/

-- Action of a functor on a hom.
-- \nearrow
infix `↗` : 100 := λ {C : Cat} {D : Cat} (F : C ⇉⇉ D) {x y : [[C]]} (f : x →→ y), F^.hom f

-- A natural transformation between functors.
structure NatTrans
    {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    (F G : C ⇉⇉ D)
    : Type (max ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂)
:= (component : ∀ (x : [[C]]), F x →→ G x)
   (transport : ∀ {x y : [[C]]} {f : x →→ y}
                , component y ∘∘ (F ↗ f)
                   = (G ↗ f) ∘∘ component x)

-- A natural transformation.
-- \rightarrowtail\rightarrowtail
infix `↣↣` : 110 := λ {C : Cat} {D : Cat} (F₁ F₂ : C ⇉⇉ D), NatTrans F₁ F₂

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
                , f₁ == f₂ → F₁ ↗ f₁ == F₂ ↗ f₂)
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

/-! #brief Composition of functors is associative.
-/
theorem Fun.comp_assoc {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}} {E : Cat.{ℓobj₄ ℓhom₄}}
    {H : D ⇉⇉ E} {G : C ⇉⇉ D} {F : B ⇉⇉ C}
    : H □□ (G □□ F) = (H □□ G) □□ F
:= rfl

/-! #brief The identity functor is a left-identity for composition.
-/
@[simp] theorem Fun.comp_id_left {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F : C ⇉⇉ D}
    : Fun.id D □□ F = F
:= begin cases F, apply rfl end

/-! #brief The identity functor is a right-identity for composition.
-/
@[simp] theorem Fun.comp_id_right {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F : C ⇉⇉ D}
    : F □□ Fun.id C = F
:= begin cases F, apply rfl end



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
@[reducible] definition NatTrans.id {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    (F : C ⇉⇉ D)
    : F ↣↣ F
:= { component := λ x, ⟨⟨F x⟩⟩
   , transport
      := λ x y f
         , by calc ⟨⟨F y⟩⟩ ∘∘ (F ↗ f)
                       = F ↗ f              : D^.circ_id_left
                   ... = (F ↗ f) ∘∘ ⟨⟨F x⟩⟩ : eq.symm D^.circ_id_right
   }

/-! #brief Composition of natural transformations.
-/
@[reducible] definition NatTrans.comp {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
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
infixl `◇◇` : 150
:= λ {C : Cat} {D : Cat} {F G H : C ⇉⇉ D}
     (ηGH : G ↣↣ H) (ηFG : F ↣↣ G)
   , NatTrans.comp ηGH ηFG

/-! #brief Composition of natural transformations is associative.
-/
theorem NatTrans.comp_assoc {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F G H J : C ⇉⇉ D}
    {ηHJ : H ↣↣ J} {ηGH : G ↣↣ H} {ηFG : F ↣↣ G}
    : ηHJ ◇◇ (ηGH ◇◇ ηFG) = (ηHJ ◇◇ ηGH) ◇◇ ηFG
:= begin
     apply NatTrans.eq,
     intro x,
     apply D^.circ_assoc
   end

/-! #brief The identity natural transformation is a left-identity for composition.
-/
@[simp] theorem NatTrans.comp_id_left {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F G : C ⇉⇉ D} {ηFG : F ↣↣ G}
    : NatTrans.id G ◇◇ ηFG = ηFG
:= begin
     apply NatTrans.eq,
     intro x,
     apply D^.circ_id_left
   end

/-! #brief The identity natural transformation is a right-identity for composition.
-/
@[simp] theorem NatTrans.comp_id_right {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F G : C ⇉⇉ D} {ηFG : F ↣↣ G}
    : ηFG ◇◇ NatTrans.id F = ηFG
:= begin
     apply NatTrans.eq,
     intro x,
     apply D^.circ_id_right
   end

/-! #brief Natural transformations can be composed with functors on the left.
-/
@[reducible] definition NatTrans.fun_comp {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    {F₁ F₂ : B ⇉⇉ C}
    (G : C ⇉⇉ D) (η : F₁ ↣↣ F₂)
    : (G □□ F₁) ↣↣ (G □□ F₂)
:= { component := λ x, G ↗ (η x)
   , transport
      := λ x y f
         , by calc (G ↗ (η y)) ∘∘ ((G □□ F₁) ↗ f)
                       = G ↗ (η y ∘∘ (F₁ ↗ f))         : eq.symm G^.hom_circ
                   ... = G ↗ ((F₂ ↗ f) ∘∘ η x)         : by rw η^.transport
                   ... = ((G □□ F₂) ↗ f) ∘∘ (G ↗ (η x)) : G^.hom_circ
   }

-- Composition of a functor with a natural transformation.
-- \Box\Diamond
infix `□◇` : 150
:= λ {B : Cat} {C : Cat} {D : Cat}
     {F₁ F₂ : B ⇉⇉ C}
     (G : C ⇉⇉ D) (η : F₁ ↣↣ F₂)
   , NatTrans.fun_comp G η

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
     dsimp,
     simp
   end

/-! #brief NatTrans.fun_comp distributes over Fun.comp.
-/
@[simp] theorem NatTrans.fun_comp_dist_left {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}} {E : Cat.{ℓobj₄ ℓhom₄}}
    {H : D ⇉⇉ E} {G : C ⇉⇉ D} {F₁ F₂ : B ⇉⇉ C} {η : F₁ ↣↣ F₂}
    : H □◇ (G □◇ η) = (H □□ G) □◇ η
:= by simp

/-! #brief Natural transformations can be composed with functors on the right.
-/
@[reducible] definition NatTrans.comp_fun {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
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

/-! #brief Functors composed with NatTrans.id on the left get absorbed.
-/
@[simp] theorem NatTrans.comp_fun_id_left {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    {G : C ⇉⇉ D} {F : B ⇉⇉ C}
    : NatTrans.id G ◇□ F = NatTrans.id (G □□ F)
:= by simp

/-! #brief Fun.id is a right-identity for NatTrans.comp_fun.
-/
@[simp] theorem NatTrans.comp_fun_id_right {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F₁ F₂ : C ⇉⇉ D} {η : F₁ ↣↣ F₂}
    : η ◇□ Fun.id C == η
:= by simp

/-! #brief NatTrans.comp_fun distributes over Fun.comp.
-/
@[simp] theorem NatTrans.comp_fun_dist_right {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}} {E : Cat.{ℓobj₄ ℓhom₄}}
    {H₁ H₂ : D ⇉⇉ E} {G : C ⇉⇉ D} {F : B ⇉⇉ C} {η : H₁ ↣↣ H₂}
    : (η ◇□ G) ◇□ F = η ◇□ (G □□ F)
:= by simp



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

-- An initial object.
structure IsInit (C : Cat.{ℓobj ℓhom})
    (x : [[C]])
    : Type (max ℓobj ℓhom)
:= (init : ∀ (y : [[C]]), x →→ y)
   (uniq : ∀ {y : [[C]]} (h : x →→ y), h = init y)

/-! #brief Every initial object can be treated as a function on objects.
-/
@[reducible] instance IsInit.has_coe_to_fun {C : Cat.{ℓobj ℓhom}}
    {x : [[C]]}
    : has_coe_to_fun (IsInit C x)
:= { F := λ x_init, ∀ (y : [[C]]), x →→ y
   , coe := λ x_init y, x_init^.init y
   }

/-! #brief Initial objects are unique up to isomorphism.

Note that the isomorphism is actually unique: indeed,
given f₁₂ : x₁ →→ x₂, f₂₁ : x₂ →→ x₁ an iso pair,
we have (by IsInit.uniq) that f₁₂ = x₁_init x₂,
and f₂₁ = x₂_init x₁.
-/
definition IsInit.iso {C : Cat.{ℓobj ℓhom}}
    {x₁ : [[C]]} (x₁_init : IsInit C x₁)
    {x₂ : [[C]]} (x₂_init : IsInit C x₂)
    : Iso (x₁_init x₂) (x₂_init x₁)
:= { id₁ := begin dsimp, rw (x₁_init^.uniq ⟨⟨x₁⟩⟩), apply x₁_init^.uniq end
   , id₂ := begin dsimp, rw (x₂_init^.uniq ⟨⟨x₂⟩⟩), apply x₂_init^.uniq end
   }

-- A final object.
structure IsFinal (C : Cat.{ℓobj ℓhom})
    (y : [[C]])
    : Type (max ℓobj ℓhom)
:= (final : ∀ (x : [[C]]), x →→ y)
   (uniq : ∀ {x : [[C]]} (h : x →→ y), h = final x)

/-! #brief Every final object can be treated as a function on objects.
-/
@[reducible] instance IsFinal.has_coe_to_fun {C : Cat.{ℓobj ℓhom}}
    {y : [[C]]}
    : has_coe_to_fun (IsFinal C y)
:= { F := λ y_final, ∀ (x : [[C]]), x →→ y
   , coe := λ y_final x, y_final^.final x
   }

/-! #brief Final objects are unique up to isomorphism.

Note that the isomorphism is actually unique: indeed,
given f₁₂ : x₁ →→ x₂, f₂₁ : x₂ →→ x₁ an iso pair,
we have (by IsFinal.uniq) that f₁₂ = x₂_final x₁,
and f₂₁ = x₁_final x₂.
-/
definition IsFinal.iso {C : Cat.{ℓobj ℓhom}}
    {x₁ : [[C]]} (x₁_final : IsFinal C x₁)
    {x₂ : [[C]]} (x₂_final : IsFinal C x₂)
    : Iso (x₂_final x₁) (x₁_final x₂)
:= { id₁ := begin dsimp, rw (x₁_final^.uniq ⟨⟨x₁⟩⟩), apply x₁_final^.uniq end
   , id₂ := begin dsimp, rw (x₂_final^.uniq ⟨⟨x₂⟩⟩), apply x₂_final^.uniq end
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
           (id_left : ∀ {c : [[C]]}, counit (L c) ∘∘ (L ↗ (unit c)) = ⟨⟨L c⟩⟩)
           (id_right : ∀ {d : [[D]]}, (R ↗ (counit d)) ∘∘ unit (R d) = ⟨⟨R d⟩⟩)

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
:= begin
     dsimp,
     rw R^.hom_circ,
     rw -C^.circ_assoc,
     rw -adj^.unit^.transport,
     rw C^.circ_assoc,
     rw adj^.id_right,
     rw C^.circ_id_left
   end

/-! #brief left_adj and right_adj are inverses of one another.
-/
@[simp] theorem Adj.left_adj_right_adj {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {L : C ⇉⇉ D} {R : D ⇉⇉ C} {adj : L ⊣ R}
    {c : [[C]]} {d : [[D]]}   {f : L c →→ d}
    : Adj.left_adj adj (Adj.right_adj adj f) = f
:= begin
     dsimp,
     rw L^.hom_circ,
     rw D^.circ_assoc,
     rw adj^.counit^.transport,
     rw -D^.circ_assoc,
     rw adj^.id_left,
     rw D^.circ_id_right
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
structure Cat.Fin (C : Cat.{ℓobj ℓhom}) : Type (max 1 ℓobj ℓhom)
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
    : Cat.{((max ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂) + 1) ((max ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂) + 1)}
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

/-! #brief The presheaf category.
-/
@[reducible] definition PreShCat (C : Cat.{ℓobj₁ ℓhom₁}) (D : Cat.{ℓobj₂ ℓhom₂})
    : Cat
:= FunCat {{C}}⁻¹ D

/-! #brief The product category.
-/
@[reducible] definition ProdCat (C : Cat.{ℓobj₁ ℓhom₁}) (D : Cat.{ℓobj₂ ℓhom₂})
    : Cat.{(max 1 ℓobj₁ ℓobj₂) (max 1 ℓhom₁ ℓhom₂)}
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
@[reducible] definition ProdCat.fst (C : Cat.{ℓobj₁ ℓhom₁}) (D : Cat.{ℓobj₂ ℓhom₂})
    : C ×× D ⇉⇉ C
:= { obj := λ x, x^.fst
   , hom := λ x y f, f^.fst
   , hom_id := λ x, rfl
   , hom_circ := λ x y z g f, rfl
   }

/-! #brief Right-projection functor from the ProdCat.
-/
@[reducible] definition ProdCat.snd (C : Cat.{ℓobj₁ ℓhom₁}) (D : Cat.{ℓobj₂ ℓhom₂})
    : C ×× D ⇉⇉ D
:= { obj := λ x, x^.snd
   , hom := λ x y f, f^.snd
   , hom_id := λ x, rfl
   , hom_circ := λ x y z g f, rfl
   }

/-! #brief Left-associate ProdCat.
-/
@[reducible] definition ProdCat.assoc_left {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}} {E : Cat.{ℓobj₃ ℓhom₃}}
    : C ×× (D ×× E) ⇉⇉ (C ×× D) ×× E
:= { obj := λ x, { fst := { fst := x^.fst, snd := x^.snd^.fst }, snd := x^.snd^.snd }
   , hom := λ x y f, { fst := { fst := f^.fst, snd := f^.snd^.fst }, snd := f^.snd^.snd }
   , hom_id := λ x, rfl
   , hom_circ := λ x y z g f, rfl
   }

/-! #brief Right-associate ProdCat.
-/
@[reducible] definition ProdCat.assoc_right {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}} {E : Cat.{ℓobj₃ ℓhom₃}}
    : (C ×× D) ×× E ⇉⇉ C ×× (D ×× E)
:= { obj := λ x, { fst := x^.fst^.fst, snd := { fst := x^.fst^.snd, snd := x^.snd } }
   , hom := λ x y f, { fst := f^.fst^.fst, snd := { fst := f^.fst^.snd, snd := f^.snd } }
   , hom_id := λ x, rfl
   , hom_circ := λ x y z g f, rfl
   }

/-! #brief The category of Lean terms in Type {ℓ} and functions between them.
-/
@[reducible] definition {ℓ} LeanCat : Cat.{(ℓ + 1) ℓ}
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
@[reducible] definition PropCat : Cat.{1 0} := LeanCat.{0}

/-! #brief The category of Lean terms in finite types.
-/
@[reducible] definition {ℓ} FinLeanCat : Cat.{(ℓ + 2) (ℓ + 1)}
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
@[reducible] definition CatCat.toLean
    : CatCat.{ℓobj ℓhom} ⇉⇉ LeanCat.{ℓobj}
:= { obj := λ C, [[C]]
   , hom := λ C D F x, F x
   , hom_id := λ C, rfl
   , hom_circ := λ B C D G F, rfl
   }

/-! #brief The Hom functor to LeanCat.
-/
@[reducible] definition HomFun (C : Cat.{ℓobj ℓhom})
    : {{C}}⁻¹ ×× C ⇉⇉ LeanCat.{ℓhom}
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

/-! #brief Homs in ObjCat.
-/
inductive {ℓ} ObjCat.Hom (A : Sort ℓ) : A → A → Sort ℓ
| id : ∀ (a : A), ObjCat.Hom a a

/-! #brief Composition in ObjCat.
-/
@[reducible] definition {ℓ} ObjCat.Hom.comp {A : Sort ℓ}
    : ∀ {x y z : A}
        (g : ObjCat.Hom A y z)
        (f : ObjCat.Hom A x y)
      , ObjCat.Hom A x z
| x .x y g (ObjCat.Hom.id .x) := g

/-! #brief A category with no nontrivial homs.
-/
@[reducible] definition {ℓ} ObjCat (A : Sort ℓ) : Cat.{ℓ ℓ}
:= { obj := A
   , hom := ObjCat.Hom A
   , id := ObjCat.Hom.id
   , circ := λ x y z g f, ObjCat.Hom.comp g f
   , circ_assoc := λ x y z w h g f, begin cases f, cases g, apply rfl end
   , circ_id_left := λ x y f, begin cases f, apply rfl end
   , circ_id_right := λ x y f, rfl
   }

/-! #brief ObjCat has no nontrivial homs.
-/
theorem {ℓ} ObjCat.hom_trivial {A : Sort ℓ}
    : ∀ {x y : [[ObjCat A]]}
        (f : (ObjCat A)^.hom x y)
      , x = y
| x .x (ObjCat.Hom.id .x) := rfl

/-! #brief ObjCat A is finite when A is.
-/
@[reducible] definition {ℓ} ObjCat.Fin {A : Sort ℓ}
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
                           apply ObjCat.Hom.id
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

/-! #brief The category with no objects.
-/
@[reducible] definition EmptyCat
    : Cat.{ℓobj ℓhom}
:= { obj := pempty.{ℓobj}
   , hom := λ x y, pempty.{ℓhom}
   , id := λ x, pempty.elim x
   , circ := λ x y z g f, f
   , circ_assoc := λ x y z w h g f, rfl
   , circ_id_left := λ x y f, rfl
   , circ_id_right := λ x y f, begin cases x end
   }

/-! #brief EmptyCat is finite.
-/
@[reducible] definition EmptyCat.Fin : Cat.Fin EmptyCat.{ℓobj ℓhom}
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
@[reducible] definition EmptyCat.IsInitial
    : IsInit CatCat.{ℓobj ℓhom} EmptyCat.{ℓobj ℓhom}
:= { init := EmptyCat.init
   , uniq
      := λ C F
         , begin
             apply Fun.eq,
             { intro x, cases x },
             { intros x y f, cases f }
           end
   }

/-! #brief The category with one object.
-/
@[reducible] definition StarCat
    : Cat.{ℓobj ℓhom}
:= { obj := punit.{ℓobj}
   , hom := λ x y, punit.{ℓhom}
   , id := λ x, punit.star
   , circ := λ x y z g f, f
   , circ_assoc := λ x y z w h g f, rfl
   , circ_id_left := λ x y f, rfl
   , circ_id_right := λ x y f, begin cases f, apply rfl end
   }

/-! #brief StarCat is finite.
-/
@[reducible] definition StarCat.Fin : Cat.Fin StarCat.{ℓobj ℓhom}
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
@[reducible] definition StarCat.IsFinal
    : IsFinal CatCat.{ℓobj ℓhom} StarCat.{ℓobj ℓhom}
:= { final := StarCat.final
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

end qp
