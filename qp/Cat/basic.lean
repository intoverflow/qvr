/- ----------------------------------------------------------------------------
The basic definitions of category theory, together with the most fundamental
properties.
---------------------------------------------------------------------------- -/


namespace qp
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

-- An object in a category.
-- [[ ]]
notation `[[` C `]]` := C^.obj

-- The identity hom at an object.
-- \langle\langle \rangle\rangle
notation `⟨⟨` x `⟩⟩` := Cat.id _ x

-- A hom in a category.
-- \to\to
infix `→→` : 110 := λ {C : Cat} (x y : [[C]]), C^.hom x y

-- Composition of hom's in a category.
-- \circ\circ
infixl `∘∘` : 150
:= λ {C : Cat} {x y z : [[C]]} (h : y →→ z) (f : x →→ y)
   , C^.circ h f


-- A functor between categories.
structure Fun (C : Cat.{ℓobj₁ ℓhom₁}) (D : Cat.{ℓobj₂ ℓhom₂})
  : Type ((max ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂) + 1)
:= (obj : [[C]] → [[D]])
   (hom : ∀ {x y : [[C]]}, x →→ y → obj x →→ obj y)
   (hom_id : ∀ {x : [[C]]}, hom ⟨⟨x⟩⟩ = ⟨⟨obj x⟩⟩)
   (hom_circ : ∀ {x y z : [[C]]}
                 {g : y →→ z} {f : x →→ y}
               , hom (g ∘∘ f) = hom g ∘∘ hom f)

attribute [simp] Fun.hom_id

-- A functor between categories.
-- \Rightarrow\Rightarrow
infix `⇒⇒` : 120 := λ (C : Cat) (D : Cat), Fun C D

/-! #brief Every functor can be treated as a function on objects.
-/
@[reducible] instance Fun.obj_has_coe_to_fun {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    : has_coe_to_fun (C ⇒⇒ D)
:= { F := λ G, [[C]] → [[D]]
   , coe := λ G x, G^.obj x
   }

/-! #brief Every functor can be treated as a function on homs.
-/
/-
instance Fun.hom_has_coe_to_fun {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    : has_coe_to_fun (C ⇒⇒ D)
:= { F := λ G, ∀ {x y : [[C]]} (f : x →→ y), G x →→ G y
   , coe := λ G x y f, G^.hom f
   }
-/

-- Action of a functor on a hom.
-- \nearrow
infix `↗` : 100 := λ {C : Cat} {D : Cat} (F : C ⇒⇒ D) {x y : [[C]]} (f : x →→ y), F^.hom f

-- A natural transformation between functors.
structure NatTrans
    {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    (F G : C ⇒⇒ D)
  : Type ((max ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂) + 1)
:= (component : ∀ (x : [[C]]), F x →→ G x)
   (transport : ∀ {x y : [[C]]} {f : x →→ y}
                , component y ∘∘ (F ↗ f)
                   = (G ↗ f) ∘∘ component x)

-- A natural transformation.
-- \rightarrowtail\rightarrowtail
infix `↣↣` : 110 := λ {C : Cat} {D : Cat} (F₁ F₂ : C ⇒⇒ D), NatTrans F₁ F₂

/-! #brief Every natural transformation can be treated as a function on objects.
-/
@[reducible] instance NatTrans.obj_has_coe_to_fun {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F₁ F₂ : C ⇒⇒ D}
    : has_coe_to_fun (F₁ ↣↣ F₂)
:= { F := λ η, ∀ (x : [[C]]), F₁ x →→ F₂ x
   , coe := λ η x, η^.component x
   }


/- ----------------------------------------------------------------------------
Functors are morphisms of categories.
---------------------------------------------------------------------------- -/

-- TODO: Fix docstring!
--/-! #brief Helper for proving two functors are equal.
---/
theorem Fun.eq {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    : ∀ {F G : C ⇒⇒ D}
        (ωobj : ∀ (x : [[C]])
                , F x = G x)
        (ωhom : ∀ {x y : [[C]]} (f : x →→ y)
                , F ↗ f == G ↗ f)
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
    : ∀ {C₁ : Cat.{ℓobj₁ ℓhom₁}} {D₁ : Cat.{ℓobj₂ ℓhom₂}} {F₁ : C₁ ⇒⇒ D₁}
        {C₂ : Cat.{ℓobj₁ ℓhom₁}} {D₂ : Cat.{ℓobj₂ ℓhom₂}} {F₂ : C₂ ⇒⇒ D₂}
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
    (G : C ⇒⇒ D) (F : B ⇒⇒ C)
    : B ⇒⇒ D
:= { obj := λ x, G (F x)
   , hom := λ x y f, G ↗ (F ↗ f)
   , hom_id := λ x, begin dsimp, simp end
   , hom_circ := λ x y z g f, begin dsimp, rw [F^.hom_circ, G^.hom_circ] end
   }

-- Composition of functors.
-- \Box\Box
infixl `□□` : 150
:= λ {B : Cat} {C : Cat} {D : Cat}
     (G : C ⇒⇒ D) (F : B ⇒⇒ C)
   , Fun.comp G F

/-! #brief Composition of functors is associative.
-/
theorem Fun.comp_assoc {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}} {E : Cat.{ℓobj₄ ℓhom₄}}
    {H : D ⇒⇒ E} {G : C ⇒⇒ D} {F : B ⇒⇒ C}
    : H □□ (G □□ F) = (H □□ G) □□ F
:= rfl

/-! #brief The identity functor is a left-identity for composition.
-/
@[simp] theorem Fun.comp_id_left {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F : C ⇒⇒ D}
    : Fun.id D □□ F = F
:= begin cases F, apply rfl end

/-! #brief The identity functor is a right-identity for composition.
-/
@[simp] theorem Fun.comp_id_right {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F : C ⇒⇒ D}
    : F □□ Fun.id C = F
:= begin cases F, apply rfl end



/- ----------------------------------------------------------------------------
Natural transformations are morphisms of functors.
---------------------------------------------------------------------------- -/

/-! #brief Helper for proving two natural transformations are equal.
-/
theorem NatTrans.eq {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}} {F G : C ⇒⇒ D}
    : ∀ {η₁ η₂ : F ↣↣ G}
        (ωcomponent : ∀ (x : [[C]])
                      , η₁ x = η₂ x)
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
    : ∀ {C₁ : Cat.{ℓobj₁ ℓhom₁}} {D₁ : Cat.{ℓobj₂ ℓhom₂}} {F₁ G₁ : C₁ ⇒⇒ D₁}
        {C₂ : Cat.{ℓobj₁ ℓhom₁}} {D₂ : Cat.{ℓobj₂ ℓhom₂}} {F₂ G₂ : C₂ ⇒⇒ D₂}
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
    (F : C ⇒⇒ D)
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
    {F G H : C ⇒⇒ D}
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
:= λ {C : Cat} {D : Cat} {F G H : C ⇒⇒ D}
     (ηGH : G ↣↣ H) (ηFG : F ↣↣ G)
   , NatTrans.comp ηGH ηFG

/-! #brief Composition of natural transformations is associative.
-/
theorem NatTrans.comp_assoc {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F G H J : C ⇒⇒ D}
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
    {F G : C ⇒⇒ D} {ηFG : F ↣↣ G}
    : NatTrans.id G ◇◇ ηFG = ηFG
:= begin
     apply NatTrans.eq,
     intro x,
     apply D^.circ_id_left
   end

/-! #brief The identity natural transformation is a right-identity for composition.
-/
@[simp] theorem NatTrans.comp_id_right {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F G : C ⇒⇒ D} {ηFG : F ↣↣ G}
    : ηFG ◇◇ NatTrans.id F = ηFG
:= begin
     apply NatTrans.eq,
     intro x,
     apply D^.circ_id_right
   end

/-! #brief Natural transformations can be composed with functors on the left.
-/
@[reducible] definition NatTrans.fun_comp {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    {F₁ F₂ : B ⇒⇒ C}
    (G : C ⇒⇒ D) (η : F₁ ↣↣ F₂)
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
     {F₁ F₂ : B ⇒⇒ C}
     (G : C ⇒⇒ D) (η : F₁ ↣↣ F₂)
   , NatTrans.fun_comp G η

/-! #brief Fun.id is a left-identity for NatTrans.fun_comp.
-/
@[simp] theorem NatTrans.fun_comp_id_left {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F₁ F₂ : C ⇒⇒ D} {η : F₁ ↣↣ F₂}
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
    {G : C ⇒⇒ D} {F : B ⇒⇒ C}
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
    {H : D ⇒⇒ E} {G : C ⇒⇒ D} {F₁ F₂ : B ⇒⇒ C} {η : F₁ ↣↣ F₂}
    : H □◇ (G □◇ η) = (H □□ G) □◇ η
:= by simp

/-! #brief Natural transformations can be composed with functors on the right.
-/
@[reducible] definition NatTrans.comp_fun {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    {G₁ G₂ : C ⇒⇒ D}
    (η : G₁ ↣↣ G₂) (F : B ⇒⇒ C)
    : (G₁ □□ F) ↣↣ (G₂ □□ F)
:= { component := λ x, η (F x)
   , transport := λ x y f, η^.transport
   }

-- Composition of a natural transformation with a functor.
-- \Diamond\Box
infix `◇□` : 150
:= λ {B : Cat} {C : Cat} {D : Cat}
     {G₁ G₂ : C ⇒⇒ D}
     (η : G₁ ↣↣ G₂) (F : B ⇒⇒ C)
   , NatTrans.comp_fun η F

/-! #brief Functors composed with NatTrans.id on the left get absorbed.
-/
@[simp] theorem NatTrans.comp_fun_id_left {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    {G : C ⇒⇒ D} {F : B ⇒⇒ C}
    : NatTrans.id G ◇□ F = NatTrans.id (G □□ F)
:= by simp

/-! #brief Fun.id is a right-identity for NatTrans.comp_fun.
-/
@[simp] theorem NatTrans.comp_fun_id_right {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F₁ F₂ : C ⇒⇒ D} {η : F₁ ↣↣ F₂}
    : η ◇□ Fun.id C == η
:= by simp

/-! #brief NatTrans.comp_fun distributes over Fun.comp.
-/
@[simp] theorem NatTrans.comp_fun_dist_right {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}} {E : Cat.{ℓobj₄ ℓhom₄}}
    {H₁ H₂ : D ⇒⇒ E} {G : C ⇒⇒ D} {F : B ⇒⇒ C} {η : H₁ ↣↣ H₂}
    : (η ◇□ G) ◇□ F = η ◇□ (G □□ F)
:= by simp


/- ----------------------------------------------------------------------------
Natural isomorphisms.
---------------------------------------------------------------------------- -/

-- A natural isomorphism.
structure NatIso {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {F₁ F₂ : C ⇒⇒ D}
    (η₁₂ : F₁ ↣↣ F₂)
    (η₂₁ : F₂ ↣↣ F₁)
    : Prop
:= (id₁ : η₂₁ ◇◇ η₁₂ = NatTrans.id F₁)
   (id₂ : η₁₂ ◇◇ η₂₁ = NatTrans.id F₂)


/- ----------------------------------------------------------------------------
Some important categories.
---------------------------------------------------------------------------- -/

-- TODO: Fix docstring!
--/-! #brief The category of categories at level {ℓobj ℓhom} and functors between them.
---/
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
:= { obj := C ⇒⇒ D
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

/-! #brief The functor from CatCat to LeanCat.
-/
@[reducible] definition CatCat.toLean
    : CatCat.{(ℓobj + 1) ℓhom} ⇒⇒ LeanCat.{ℓobj}
:= { obj := λ C, [[C]]
   , hom := λ C D F x, F x
   , hom_id := λ C, rfl
   , hom_circ := λ B C D G F, rfl
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

/-! #brief The product category.
-/
@[reducible] definition ProdCat (C : Cat.{ℓobj₁ ℓhom₁}) (D : Cat.{ℓobj₂ ℓhom₂})
    : Cat.{(max 1 ℓobj₁ ℓobj₂) (max 1 ℓhom₁ ℓhom₂)}
:= { obj := [[C]] × [[D]]
   , hom := λ x y, (x^.fst →→ y^.fst) × (x^.snd →→ y^.snd)
   , id  := λ x, (⟨⟨x^.fst⟩⟩, ⟨⟨x^.snd⟩⟩)
   , circ := λ x y z g f, (g^.fst ∘∘ f^.fst, g^.snd ∘∘ f^.snd)
   , circ_assoc
      := λ x y z w h g f
         , begin dsimp, rw [C^.circ_assoc, D^.circ_assoc] end
   , circ_id_left := λ x y f, begin dsimp, simp, cases f , apply rfl end
   , circ_id_right := λ x y f, begin dsimp, simp, cases f , apply rfl end
   }

-- The product category.
-- \times\times
infixl `××` : 130 := λ C D, ProdCat C D

/-! #brief Left-projection functor from the ProdCat.
-/
@[reducible] definition ProdCat.fst (C : Cat.{ℓobj₁ ℓhom₁}) (D : Cat.{ℓobj₂ ℓhom₂})
    : C ×× D ⇒⇒ C
:= { obj := λ x, x^.fst
   , hom := λ x y f, f^.fst
   , hom_id := λ x, rfl
   , hom_circ := λ x y z g f, rfl
   }

/-! #brief Right-projection functor from the ProdCat.
-/
@[reducible] definition ProdCat.snd (C : Cat.{ℓobj₁ ℓhom₁}) (D : Cat.{ℓobj₂ ℓhom₂})
    : C ×× D ⇒⇒ D
:= { obj := λ x, x^.snd
   , hom := λ x y f, f^.snd
   , hom_id := λ x, rfl
   , hom_circ := λ x y z g f, rfl
   }


/- ----------------------------------------------------------------------------
Boxed morphisms.
---------------------------------------------------------------------------- -/

namespace Cat
-- A hom in a category, boxed up with its domain and codomain.
structure BxHom (C : Cat.{ℓobj ℓhom}) : Type (max 1 ℓobj ℓhom)
:= (dom : [[C]])
   (codom : [[C]])
   (hom : dom →→ codom)

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

end qp
