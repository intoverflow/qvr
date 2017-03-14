/- -----------------------------------------------------------------------
Categories.
----------------------------------------------------------------------- -/

import ...p0_stdlib

namespace qp

open stdaux

universe variables ℓ ℓobj ℓhom ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂

/-! #brief A strict category.
-/
structure Cat
    : Type ((max ℓobj ℓhom) + 1)
:= (obj
    : Type ℓobj)
   (hom
     : ∀ (x y : obj)
       , Sort ℓhom)
   (id
     : ∀ (x : obj)
       , hom x x)
   (circ
     : ∀ {x y z : obj}
       , hom y z → hom x y → hom x z)
   (circ_assoc
     : ∀ {x y z w : obj}
          {h : hom z w} {g : hom y z} {f : hom x y}
       , circ h (circ g f) = circ (circ h g) f)
   (circ_id_left
     : ∀ {x y : obj} {f : hom x y}
       , circ (id y) f = f)
   (circ_id_right
     : ∀ {x y : obj} {f : hom x y}
       , circ f (id x) = f)

attribute [simp] Cat.circ_id_left
attribute [simp] Cat.circ_id_right

/-! #brief Equality of categories.
-/
theorem Cat.eq
    : ∀ {C₁ C₂ : Cat.{ℓobj ℓhom}}
      , C₁^.obj = C₂^.obj
      → C₁^.hom == C₂^.hom
      → C₁^.id == C₂^.id
      → @Cat.circ C₁ == @Cat.circ C₂
      → C₁ = C₂
| C₁ C₂ ωobj ωhom ωid ωcirc
:= begin
     cases C₁ with obj₁ hom₁ id₁ circ₁ ω₁₁ ω₁₂ ω₁₃,
     cases C₂ with obj₂ hom₂ id₂ circ₂ ω₂₁ ω₂₂ ω₂₃,
     simp at ωobj, subst ωobj,
     simp at ωhom, cases ωhom,
     simp at ωid, cases ωid,
     simp at ωcirc, cases ωcirc,
     exact rfl
   end

-- An object in a category.
-- \[[ \]]
notation `⟦` C `⟧` := Cat.obj C

-- The identity hom at an object.
-- \langle\langle \rangle\rangle
notation `⟨⟨` x `⟩⟩` := Cat.id _ x

-- A hom in a category.
-- \[[ : \to\to \]]
notation `⟦` C ` : ` x ` →→ ` y `⟧` := Cat.hom C x y

-- Composition of hom's in a category.
-- \o\o
infixl `∘∘` : 100 := Cat.circ _

/-! #brief A finite category.
-/
class Cat.Finite (C : Cat.{ℓobj ℓhom})
    : Type (max ℓobj ℓhom)
:= (obj_fin : FinType C^.obj)
   (hom_fin : ∀ (x y : C^.obj), FinSort (C^.hom x y))

attribute [instance] Cat.Finite.obj_fin
attribute [instance] Cat.Finite.hom_fin



/- -----------------------------------------------------------------------
The empty and star categories.
----------------------------------------------------------------------- -/

/-! #brief The category with one object and one hom.
-/
definition UnitCat : Cat.{ℓobj ℓhom}
:= { obj := punit
   , hom := λ u₁ u₂, punit
   , id := λ u, punit.star
   , circ := λ u₁ u₂ u₃ g f, punit.star
   , circ_assoc := λ u₁ u₂ u₃ u₄ h g f, rfl
   , circ_id_left := λ u₁ u₂ f, begin cases f, trivial end
   , circ_id_right := λ u₁ u₂ f, begin cases f, trivial end
   }

/-! #brief UnitCat is a finite category.
-/
instance UnitCat.Finite
    : Cat.Finite (UnitCat.{ℓobj ℓhom})
:= { obj_fin := punit.FinSort
   , hom_fin := λ u₁ u₂, punit.FinSort
   }

/-! #brief The category with no objects.
-/
definition EmptyCat : Cat.{ℓobj ℓhom}
:= { obj := pempty
   , hom := λ u₁ u₂, pempty
   , id := λ u, by cases u
   , circ := λ u₁ u₂ u₃ g f, by cases f
   , circ_assoc := λ u₁ u₂ u₃ u₄ h g f, by cases f
   , circ_id_left := λ u₁ u₂ f, by cases f
   , circ_id_right := λ u₁ u₂ f, by cases f
   }

/-! #brief EmptyCat is a finite category.
-/
instance EmptyCat.Finite
    : Cat.Finite (EmptyCat.{ℓobj ℓhom})
:= { obj_fin := pempty.FinSort
   , hom_fin := λ u₁ u₂, pempty.FinSort
   }



/- -----------------------------------------------------------------------
The Lean categories.
----------------------------------------------------------------------- -/

/-! #brief The category of Lean sorts at level ℓ.
-/
definition SortCat : Cat.{ℓ ℓ}
:= { obj := Sort.{ℓ}
   , hom := λ X Y, X → Y
   , id := λ X x, x
   , circ := λ X Y Z g f x, g (f x)
   , circ_assoc := λ X Y Z W h g f, rfl
   , circ_id_left := λ X Y f, rfl
   , circ_id_right := λ X Y f, rfl
   }

/-! #brief The category of Lean propositions.
-/
definition PropCat : Cat.{0 0}
:= SortCat.{0}

example : PropCat^.obj := true

/-! #brief The category of Lean types at level ℓ.
-/
definition LeanCat : Cat.{(ℓ + 1) (ℓ + 1)}
:= SortCat.{ℓ + 1}

example : LeanCat.{0}^.obj := ℕ
example : LeanCat.{1}^.obj := ℕ → LeanCat.{0}^.obj
example : LeanCat.{ℓ}^.obj := punit
example : LeanCat.{ℓ}^.obj := list punit



/- -----------------------------------------------------------------------
Categories which box up certain theories.
----------------------------------------------------------------------- -/

/-! #brief The category of relations and monotone functions.
-/
definition CatOfRels : Cat.{(ℓ + 1) (ℓ + 1)}
:= { obj := Σ (A : Type ℓ), (A → A → Prop)
   , hom := λ A B, { f : A^.fst → B^.fst // monotone A^.snd B^.snd f }
   , id := λ A, { val := id, property := id.monotone A^.snd }
   , circ := λ A B C g f, { val := λ a, g^.val (f^.val a)
                          , property := begin
                                          intros a₁ a₂ ω,
                                          apply g^.property,
                                          apply f^.property,
                                          exact ω
                                        end
                          }
   , circ_assoc := λ A B C D h g f, subtype.eq rfl
   , circ_id_left := λ A B f, subtype.eq rfl
   , circ_id_right := λ A B f, subtype.eq rfl
   }

/-! #brief The category of preorders and monotone functions.
-/
definition CatOfPreorders : Cat.{(ℓ + 1) (ℓ + 1)}
:= { obj := { A : Σ (A : Type ℓ), (A → A → Prop) // reflexive A^.snd ∧ transitive A^.snd }
   , hom := λ A B, { f : A^.val^.fst → B^.val^.fst // monotone A^.val^.snd B^.val^.snd f }
   , id := λ A, { val := id, property := id.monotone A^.val^.snd }
   , circ := λ A B C g f, { val := λ a, g^.val (f^.val a)
                          , property := begin
                                          intros a₁ a₂ ω,
                                          apply g^.property,
                                          apply f^.property,
                                          exact ω
                                        end
                          }
   , circ_assoc := λ A B C D h g f, subtype.eq rfl
   , circ_id_left := λ A B f, subtype.eq rfl
   , circ_id_right := λ A B f, subtype.eq rfl
   }

/-! #brief The category of semigroups.
-/
definition CatOfSemigroups : Cat.{(ℓ + 1) (ℓ + 1)}
:= { obj := Σ (A : Type ℓ), semigroup A
   , hom := λ A B, { f : A^.fst → B^.fst // @semigroup.hom _ A^.snd _ B^.snd f }
   , id := λ A, { val := id, property := @semigroup.hom_id _ A^.snd }
   , circ := λ A B C g f, { val := λ a, g^.val (f^.val a)
                          , property := @semigroup.hom_comp
                                         _ A^.snd _ B^.snd _ C^.snd
                                         _ g^.property _ f^.property
                          }
   , circ_assoc := λ A B C D h g f, subtype.eq rfl
   , circ_id_left := λ A B f, subtype.eq rfl
   , circ_id_right := λ A B f, subtype.eq rfl
   }

/-! #brief The category of monoids.
-/
definition CatOfMonoids : Cat.{(ℓ + 1) (ℓ + 1)}
:= { obj := Σ (A : Type ℓ), monoid A
   , hom := λ A B, { f : A^.fst → B^.fst // @monoid.hom _ A^.snd _ B^.snd f }
   , id := λ A, { val := id, property := @monoid.hom_id _ A^.snd }
   , circ := λ A B C g f, { val := λ a, g^.val (f^.val a)
                          , property := @monoid.hom_comp
                                         _ A^.snd _ B^.snd _ C^.snd
                                         _ g^.property _ f^.property
                          }
   , circ_assoc := λ A B C D h g f, subtype.eq rfl
   , circ_id_left := λ A B f, subtype.eq rfl
   , circ_id_right := λ A B f, subtype.eq rfl
   }

/-! #brief The category of groups.
-/
definition CatOfGroups : Cat.{(ℓ + 1) (ℓ + 1)}
:= { obj := Σ (A : Type ℓ), group A
   , hom := λ A B, { f : A^.fst → B^.fst // @group.hom _ A^.snd _ B^.snd f }
   , id := λ A, { val := id, property := @group.hom_id _ A^.snd }
   , circ := λ A B C g f, { val := λ a, g^.val (f^.val a)
                          , property := @group.hom_comp
                                         _ A^.snd _ B^.snd _ C^.snd
                                         _ g^.property _ f^.property
                          }
   , circ_assoc := λ A B C D h g f, subtype.eq rfl
   , circ_id_left := λ A B f, subtype.eq rfl
   , circ_id_right := λ A B f, subtype.eq rfl
   }

/-! #brief The category of commutative rings.
-/
definition CatOfCommRings : Cat.{(ℓ + 1) (ℓ + 1)}
:= { obj := Σ (A : Type ℓ), comm_ring A
   , hom := λ A B, { f : A^.fst → B^.fst // @comm_ring.hom _ A^.snd _ B^.snd f }
   , id := λ A, { val := id, property := @comm_ring.hom_id _ A^.snd }
   , circ := λ A B C g f, { val := λ a, g^.val (f^.val a)
                          , property := @comm_ring.hom_comp
                                         _ A^.snd _ B^.snd _ C^.snd
                                         _ g^.property _ f^.property
                          }
   , circ_assoc := λ A B C D h g f, subtype.eq rfl
   , circ_id_left := λ A B f, subtype.eq rfl
   , circ_id_right := λ A B f, subtype.eq rfl
   }



/- -----------------------------------------------------------------------
Categories induced by monoids and groups.
----------------------------------------------------------------------- -/

/-! #brief A monoid category.
-/
definition MonoidCat (A : Type ℓ) [A_monoid : monoid A]
    : Cat.{(ℓ + 1) (ℓ + 1)}
:= { obj := punit
   , hom := λ u₁ u₂, A
   , id := λ u, 1
   , circ := λ u₁ u₂ u₃ g f, g * f
   , circ_assoc := λ u₁ u₂ u₃ u₄ h g f, eq.symm (mul_assoc h g f)
   , circ_id_left := λ u₁ u₂ f, one_mul f
   , circ_id_right := λ u₁ u₂ f, mul_one f
   }

/-! #brief A group category.
-/
definition GroupCat (A : Type ℓ) [A_group : group A]
    : Cat.{(ℓ + 1) (ℓ + 1)}
:= MonoidCat A



/- -----------------------------------------------------------------------
Preorder categories and categories of objects.
----------------------------------------------------------------------- -/

/-! #brief A preorder category.
-/
definition PreorderCat {A : Type ℓ}
    (r : A → A → Prop)
    (r_refl : reflexive r)
    (r_trans : transitive r)
    : Cat.{ℓ 0}
:= { obj := A
   , hom := r
   , id := r_refl
   , circ := λ a₁ a₂ a₃ g f, r_trans f g
   , circ_assoc := λ a₁ a₂ a₃ a₄ h g f, proof_irrel _ _
   , circ_id_left := λ a₁ a₂ f, proof_irrel _ _
   , circ_id_right := λ a₁ a₂ f, proof_irrel _ _
   }

/-! #brief The category of natural numbers, ordered by nat.le
-/
definition NatCat : Cat.{0 0}
:= PreorderCat nat.le @nat.le_refl @nat.le_trans

/-! #brief Decidable preorders on finite types induce finite categories.
-/
instance PreorderCat.Finite {A : Type ℓ}
    (r : A → A → Prop)
    (r_refl : reflexive r)
    (r_trans : transitive r)
    [A_FinType : FinType A]
    [r_decidable : decidable_rel r]
    : Cat.Finite (PreorderCat r r_refl r_trans)
:= { obj_fin := A_FinType
   , hom_fin := λ a₁ a₂, @Prop.decidable_FinSort (r a₁ a₂) (r_decidable a₁ a₂)
   }

/-! #brief A category of objects.
-/
definition ObjCat (A : Type ℓ)
    : Cat.{ℓ 0}
:= PreorderCat (@eq A) (@eq.refl A) (@eq.trans A)

/-! #brief Finite types with decidable equality yield finite object categories.
-/
instance ObjCat.Finite (A : Type ℓ)
    [A_FinType : FinType A]
    [A_decidable_eq : decidable_eq A]
    : Cat.Finite (ObjCat A)
:= PreorderCat.Finite (@eq A) (@eq.refl A) (@eq.trans A)

/-! #brief The finite category with N objects.
-/
definition FinCat (N : ℕ) : Cat.{0 0}
:= ObjCat (fin N)

/-! #brief The finite category is finite.
-/
instance FinCat.Finite (N : ℕ)
    : Cat.Finite (FinCat N)
:= ObjCat.Finite (fin N)



/- -----------------------------------------------------------------------
Product categories.
----------------------------------------------------------------------- -/

/-! #brief The product category.
-/
definition ProdCat (C : Cat.{ℓobj₁ ℓhom₁}) (D : Cat.{ℓobj₂ ℓhom₂})
    : Cat.{(max ℓobj₁ ℓobj₂) (max 1 ℓhom₁ ℓhom₂)}
:= { obj := prod C^.obj D^.obj
   , hom := λ cd₁ cd₂, pprod (C^.hom cd₁^.fst cd₂^.fst)
                            (D^.hom cd₁^.snd cd₂^.snd)
   , id := λ cd, { fst := C^.id cd^.fst
                 , snd := D^.id cd^.snd
                 }
   , circ := λ x y z g f, { fst := C^.circ g^.fst f^.fst
                          , snd := D^.circ g^.snd f^.snd
                          }
   , circ_assoc := λ x y z w h g f, by rw [C^.circ_assoc, D^.circ_assoc]
   , circ_id_left := λ x y f, begin cases f, simp end
   , circ_id_right := λ x y f, begin cases f, simp end
   }

-- A product category.
-- \times\times
infixr `××` : 200 := ProdCat



/- -----------------------------------------------------------------------
Opposite categories.
----------------------------------------------------------------------- -/

/-! #brief The opposite category.
-/
@[reducible] definition OpCat (C : Cat.{ℓobj ℓhom})
    : Cat.{ℓobj ℓhom}
:= { obj := C^.obj
   , hom := λ x y, C^.hom y x
   , id := λ x, C^.id x
   , circ := λ x y z g f, C^.circ f g
   , circ_assoc := λ x y z w h g f, eq.symm C^.circ_assoc
   , circ_id_left := λ x y f, C^.circ_id_right
   , circ_id_right := λ x y f, C^.circ_id_left
   }

-- An opposite category.
-- \inv
notation C `⁻¹` := OpCat C

/-! #brief OpCat is an involution.
-/
theorem OpCat_OpCat (C : Cat.{ℓobj ℓhom})
    : OpCat (OpCat C) = C
:= begin
     apply Cat.eq,
     { trivial },
     { trivial },
     { trivial },
     { trivial }
   end

/-! #brief OpCat distributes over ProdCat.
-/
theorem OpCat_ProdCat (C : Cat.{ℓobj₁ ℓhom₁}) (D : Cat.{ℓobj₂ ℓhom₂})
    : OpCat (ProdCat C D) = ProdCat (OpCat C) (OpCat D)
:= begin
     apply Cat.eq,
     { trivial },
     { trivial },
     { trivial },
     { trivial }
   end



/- -----------------------------------------------------------------------
Over and under categories.
----------------------------------------------------------------------- -/

/-! #brief An object in an over category.
-/
structure OverObj (C : Cat.{ℓobj ℓhom}) (X : C^.obj)
    : Type (max ℓobj ℓhom)
:= (obj : C^.obj)
   (hom : C^.hom obj X)

/-! #brief The object contained within an over object.
-/
@[reducible] definition OverObj.dom {C : Cat.{ℓobj ℓhom}} {X : C^.obj}
    (A : OverObj C X)
    : C^.obj
:= A^.obj

/-! #brief The hom contained within an over object.
-/
@[reducible] definition OverObj.down {C : Cat.{ℓobj ℓhom}} {X : C^.obj}
    (A : OverObj C X)
    : C^.hom (OverObj.dom A) X
:= A^.hom

/-! #brief Eqaulity of objects in an over category.
-/
theorem OverObj.eq {C : Cat.{ℓobj ℓhom}} {X : C^.obj}
    : ∀ {A B : OverObj C X}
         (ωobj : A^.dom = B^.dom)
         (ωhom : A^.down == B^.down)
      , A = B
| (OverObj.mk obj hom) (OverObj.mk .obj .hom)
  (eq.refl .obj) (heq.refl .hom)
:= rfl

/-! #brief A hom in an over category.
-/
structure OverHom (C : Cat.{ℓobj ℓhom}) (X : C^.obj)
    (A B : OverObj C X)
    : Sort (max 1 ℓhom)
:= (hom : C^.hom A^.dom B^.dom)
   (triangle : A^.down = C^.circ B^.down hom)

/-! #brief Equality of homs in an over category.
-/
theorem OverHom.eq {C : Cat.{ℓobj ℓhom}} {X : C^.obj}
    {A B : OverObj C X}
    : ∀ {f₁ f₂ : OverHom C X A B}
      , f₁^.hom = f₂^.hom
      → f₁ = f₂
| (OverHom.mk hom ω₁) (OverHom.mk .hom ω₂) (eq.refl .hom)
:= rfl

/-! #brief Heterogeneous equality of homs in an over category.
-/
theorem OverHom.heq {C : Cat.{ℓobj ℓhom}} {X : C^.obj}
    : ∀ {A₁ B₁ A₂ B₂ : OverObj C X}
         {f₁ : OverHom C X A₁ B₁}
         {f₂ : OverHom C X A₂ B₂}
      , A₁ = A₂ → B₁ = B₂ → f₁^.hom == f₂^.hom
      → f₁ == f₂
| (OverObj.mk a fa) (OverObj.mk b fb) (OverObj.mk .a .fa) (OverObj.mk .b .fb)
  (OverHom.mk f ωf₁) (OverHom.mk .f ωf₂) (eq.refl ._) (eq.refl ._) (heq.refl ._)
:= heq.refl _

/-! #brief The identity hom in an over category.
-/
definition OverHom.id (C : Cat.{ℓobj ℓhom}) (X : C^.obj)
    (A : OverObj C X)
    : OverHom C X A A
:= { hom := C^.id A^.dom
   , triangle := eq.symm C^.circ_id_right
   }

/-! #brief Composition of homs in an over category.
-/
definition OverHom.comp (C : Cat.{ℓobj ℓhom}) (X : C^.obj)
    (P Q R : OverObj C X)
    (g : OverHom C X Q R)
    (f : OverHom C X P Q)
    : OverHom C X P R
:= { hom := C^.circ g^.hom f^.hom
   , triangle := by rw [f^.triangle, g^.triangle, C^.circ_assoc]
   }

/-! #brief Associativity of hom composition in an over category.
-/
theorem OverHom.comp_assoc (C : Cat.{ℓobj ℓhom}) (X : C^.obj)
    (P Q R S : OverObj C X)
    (h : OverHom C X R S)
    (g : OverHom C X Q R)
    (f : OverHom C X P Q)
    : OverHom.comp C X _ _ _ h (OverHom.comp C X _ _ _ g f)
       = OverHom.comp C X _ _ _ (OverHom.comp C X _ _ _ h g) f
:= begin
     apply OverHom.eq,
     exact C^.circ_assoc
   end

/-! #brief Left-identity of hom composition in an over category.
-/
theorem OverHom.comp_id_left (C : Cat.{ℓobj ℓhom}) (X : C^.obj)
    (P Q : OverObj C X)
    (f : OverHom C X P Q)
    : OverHom.comp C X _ _ _ (OverHom.id C X _) f = f
:= begin
     apply OverHom.eq,
     exact C^.circ_id_left
   end

/-! #brief Right-identity of hom composition in an over category.
-/
theorem OverHom.comp_id_right (C : Cat.{ℓobj ℓhom}) (X : C^.obj)
    (P Q : OverObj C X)
    (f : OverHom C X P Q)
    : OverHom.comp C X _ _ _ f (OverHom.id C X _) = f
:= begin
     apply OverHom.eq,
     exact C^.circ_id_right
   end

/-! #brief An over category.
-/
definition OverCat (C : Cat.{ℓobj ℓhom}) (X : C^.obj)
    : Cat.{(max ℓobj ℓhom) (max 1 ℓhom)}
:= { obj := OverObj C X
   , hom := OverHom C X
   , id := OverHom.id C X
   , circ := OverHom.comp C X
   , circ_assoc := OverHom.comp_assoc C X
   , circ_id_left := OverHom.comp_id_left C X
   , circ_id_right := OverHom.comp_id_right C X
   }

-- An over category.
-- //
notation C `//` X := OverCat C X

/-! #brief An under category.
-/
definition UnderCat (C : Cat.{ℓobj ℓhom}) (X : C^.obj)
    : Cat.{(max ℓobj ℓhom) (max 1 ℓhom)}
--:= OpCat (OverCat (OpCat C) X)
:= OpCat (OverCat (OpCat C) X)

-- An under category.
-- \\
notation C `\\` X := UnderCat C X

/-! #brief An object in an under category.
-/
definition UnderObj (C : Cat.{ℓobj ℓhom}) (X : C^.obj)
    : Type (max ℓobj ℓhom)
:= (UnderCat C X)^.obj

/-! #brief A hom in an under category.
-/
definition UnderHom (C : Cat.{ℓobj ℓhom}) (X : C^.obj)
    (A B : UnderObj C X)
    : Sort (max 1 ℓhom)
:= (UnderCat C X)^.hom A B

/-! #brief Constructor for an object in an under category.
-/
definition UnderObj.mk {C : Cat.{ℓobj ℓhom}} {X : C^.obj}
    {A : C^.obj} (f : C^.hom X A)
    : UnderObj C X
:= { obj := A, hom := f }

/-! #brief The object contained within an under object.
-/
@[reducible] definition UnderObj.codom {C : Cat.{ℓobj ℓhom}} {X : C^.obj}
    (A : UnderObj C X)
    : C^.obj
:= A^.obj

/-! #brief The hom contained within an under object.
-/
@[reducible] definition UnderObj.up {C : Cat.{ℓobj ℓhom}} {X : C^.obj}
    (A : UnderObj C X)
    : C^.hom X (UnderObj.codom A)
:= A^.hom

/-! #brief Constructor for a hom in an under category.
-/
definition UnderHom.mk {C : Cat.{ℓobj ℓhom}} {X : C^.obj}
    {A B : UnderObj C X}
    (f : C^.hom (UnderObj.codom A) (UnderObj.codom B))
    (ω : B^.up = C^.circ f A^.up)
    : UnderHom C X A B
:= { hom := f, triangle := ω }

/-! #brief The hom contained within an under hom.
-/
@[reducible] definition UnderHom.hom {C : Cat.{ℓobj ℓhom}} {X : C^.obj}
    {A B : UnderObj C X}
    (f : UnderHom C X A B)
    : C^.hom (UnderObj.codom A) (UnderObj.codom B)
:= f^.hom

/-! #brief The hom contained within an under hom.
-/
@[reducible] theorem UnderHom.triangle {C : Cat.{ℓobj ℓhom}} {X : C^.obj}
    (A B : UnderObj C X)
    (f : UnderHom C X A B)
    : B^.up = UnderHom.hom f ∘∘ A^.up
:= f^.triangle



/- -----------------------------------------------------------------------
Isomorphisms in categories.
----------------------------------------------------------------------- -/

/-! #brief An isomorphism in a category.
-/
structure Iso {C : Cat.{ℓobj ℓhom}}
    {c₁ c₂ : C^.obj}
    (f : C^.hom c₁ c₂) (g : C^.hom c₂ c₁)
    : Prop
:= (id₁ : C^.circ g f = C^.id c₁)
   (id₂ : C^.circ f g = C^.id c₂)

/-! #brief Iso's can be 'flipped' to run in the other direction.
-/
definition Iso.flip {C : Cat.{ℓobj ℓhom}}
    {c₁ c₂ : C^.obj}
    {f : C^.hom c₁ c₂} {g : C^.hom c₂ c₁}
    (iso : Iso f g)
    : Iso g f
:= { id₁ := iso^.id₂
   , id₂ := iso^.id₁
   }

/-! #brief Iso's have unique inverses.
-/
definition Iso.inv_uniq₂ {C : Cat.{ℓobj ℓhom}}
    {c₁ c₂ : C^.obj}
    {f : C^.hom c₁ c₂} {g₁ g₂ : C^.hom c₂ c₁}
    (iso₁ : Iso f g₁)
    (iso₂ : Iso f g₂)
    : g₁ = g₂
:= by calc g₁  = g₁ ∘∘ ⟨⟨c₂⟩⟩    : by rw C^.circ_id_right
           ... = g₁ ∘∘ (f ∘∘ g₂) : by rw iso₂^.id₂
           ... = (g₁ ∘∘ f) ∘∘ g₂ : by rw C^.circ_assoc
           ... = ⟨⟨c₁⟩⟩ ∘∘ g₂    : by rw iso₁^.id₁
           ... = g₂              : by rw C^.circ_id_left

/-! #brief Iso's have unique inverses.
-/
definition Iso.inv_uniq₁ {C : Cat.{ℓobj ℓhom}}
    {c₁ c₂ : C^.obj}
    {f₁ f₂ : C^.hom c₁ c₂} {g : C^.hom c₂ c₁}
    (iso₁ : Iso f₁ g)
    (iso₂ : Iso f₂ g)
    : f₁ = f₂
:= Iso.inv_uniq₂ (Iso.flip iso₁) (Iso.flip iso₂)

/-! #brief Identity homs are isomorphisms.
-/
theorem Cat.id.Iso {C : Cat.{ℓobj ℓhom}}
    (c : C^.obj)
    : Iso (C^.id c) (C^.id c)
:= { id₁ := C^.circ_id_left
   , id₂ := C^.circ_id_left
   }

/-! #brief Isomorphisms are closed under composition.
-/
theorem Cat.circ.Iso {C : Cat.{ℓobj ℓhom}}
    {c₁ c₂ c₃ : C^.obj}
    {f₂₃ : C^.hom c₂ c₃} {g₂₃ : C^.hom c₃ c₂} (iso₂₃ : Iso f₂₃ g₂₃)
    {f₁₂ : C^.hom c₁ c₂} {g₁₂ : C^.hom c₂ c₁} (iso₁₂ : Iso f₁₂ g₁₂)
    : Iso (C^.circ f₂₃ f₁₂) (C^.circ g₁₂ g₂₃)
:= { id₁ := by calc g₁₂ ∘∘ g₂₃ ∘∘ (f₂₃ ∘∘ f₁₂)
                        = g₁₂ ∘∘ (g₂₃ ∘∘ f₂₃) ∘∘ f₁₂ : by repeat {rw C^.circ_assoc}
                    ... = g₁₂ ∘∘ ⟨⟨c₂⟩⟩ ∘∘ f₁₂       : by rw iso₂₃^.id₁
                    ... = g₁₂ ∘∘ f₁₂                 : by rw C^.circ_id_right
                    ... = ⟨⟨c₁⟩⟩                     : by rw iso₁₂^.id₁
   , id₂ := by calc f₂₃ ∘∘ f₁₂ ∘∘ (g₁₂ ∘∘ g₂₃)
                        = f₂₃ ∘∘ (f₁₂ ∘∘ g₁₂) ∘∘ g₂₃ : by repeat {rw C^.circ_assoc}
                    ... = f₂₃ ∘∘ ⟨⟨c₂⟩⟩ ∘∘ g₂₃       : by rw iso₁₂^.id₂
                    ... = f₂₃ ∘∘ g₂₃                 : by rw C^.circ_id_right
                    ... = ⟨⟨c₃⟩⟩                     : by rw iso₂₃^.id₂
   }



/- -----------------------------------------------------------------------
Initial and final objects in categories.
----------------------------------------------------------------------- -/

/-! #brief A final object in a category.
-/
structure Final (C : Cat.{ℓobj ℓhom})
    : Type (max ℓobj ℓhom)
:= (obj : C^.obj)
   (hom : ∀ (c : C^.obj), C^.hom c obj)
   (hom_uniq : ∀ {c : C^.obj} {h : C^.hom c obj}, h = hom c )

/-! #brief A category with a final object.
-/
class HasFinal (C : Cat.{ℓobj ℓhom})
    : Type (max ℓobj ℓhom)
:= (final : Final C)

/-! #brief The final object in a category with a final object.
-/
definition final (C : Cat.{ℓobj ℓhom})
    [C_HasFinal : HasFinal C]
    : C^.obj
:= (HasFinal.final C)^.obj

/-! #brief The final hom in a category with a final object.
-/
definition final_hom {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    (c : C^.obj)
    : C^.hom c (final C)
:= (HasFinal.final C)^.hom c

/-! #brief The final hom is unique.
-/
definition final_hom_uniq (C : Cat.{ℓobj ℓhom})
    [C_HasFinal : HasFinal C]
    {c : C^.obj} {f : C^.hom c (final C)}
    : f = final_hom c
:= (HasFinal.final C)^.hom_uniq

/-! #brief HasFinal is non-evil.
-/
theorem HasFinal_nonevil {C : Cat.{ℓobj ℓhom}}
    (C_HasFinal₁ C_HasFinal₂ : HasFinal C)
    : Iso (@final_hom _ C_HasFinal₁ (@final _ C_HasFinal₂))
          (@final_hom _ C_HasFinal₂ (@final _ C_HasFinal₁))
:= { id₁ := eq.trans (@final_hom_uniq _ C_HasFinal₂ _ _)
                     (eq.symm (@final_hom_uniq _ C_HasFinal₂ _ _))
   , id₂ := eq.trans (@final_hom_uniq _ C_HasFinal₁ _ _)
                     (eq.symm (@final_hom_uniq _ C_HasFinal₁ _ _))
   }

/-! #brief HasFinal is non-evil.
-/
theorem HasFinal_nonevil.uniq₁ {C : Cat.{ℓobj ℓhom}}
    (C_HasFinal₁ C_HasFinal₂ : HasFinal C)
    {f : C^.hom (@final _ C_HasFinal₂) (@final _ C_HasFinal₁)}
    {g : C^.hom (@final _ C_HasFinal₁) (@final _ C_HasFinal₂)}
    (iso : Iso f g)
    : f = (@final_hom _ C_HasFinal₁ (@final _ C_HasFinal₂))
:= @final_hom_uniq _ C_HasFinal₁ _ _

/-! #brief HasFinal is non-evil.
-/
theorem HasFinal_nonevil.uniq₂ {C : Cat.{ℓobj ℓhom}}
    (C_HasFinal₁ C_HasFinal₂ : HasFinal C)
    {f : C^.hom (@final _ C_HasFinal₂) (@final _ C_HasFinal₁)}
    {g : C^.hom (@final _ C_HasFinal₁) (@final _ C_HasFinal₂)}
    (iso : Iso f g)
    : g = (@final_hom _ C_HasFinal₂ (@final _ C_HasFinal₁))
:= @final_hom_uniq _ C_HasFinal₂ _ _


/-! #brief An initial object in a category.
-/
definition Init (C : Cat.{ℓobj ℓhom})
    : Type (max ℓobj ℓhom)
:= Final (OpCat C)

/-! #brief A category with an initial object.
-/
class HasInit (C : Cat.{ℓobj ℓhom})
    : Type (max ℓobj ℓhom)
:= (init : Init C)

/-! #brief The initial object in a category with a initial object.
-/
definition init (C : Cat.{ℓobj ℓhom})
    [C_HasInit : HasInit C]
    : C^.obj
:= (HasInit.init C)^.obj

/-! #brief The initial hom in a category with a initial object.
-/
definition init_hom {C : Cat.{ℓobj ℓhom}}
    [C_HasInit : HasInit C]
    (c : C^.obj)
    : C^.hom (init C) c
:= (HasInit.init C)^.hom c

/-! #brief The initial hom is unique.
-/
definition init_hom_uniq (C : Cat.{ℓobj ℓhom})
    [C_HasInit : HasInit C]
    {c : C^.obj} {f : C^.hom (init C) c}
    : f = init_hom c
:= (HasInit.init C)^.hom_uniq

/-! #brief Initial and final are dual concepts.
-/
theorem Init_dual_Final (C : Cat.{ℓobj ℓhom})
    : Init C = Final (OpCat C)
:= rfl

/-! #brief Final and initial are dual concepts.
-/
theorem Final_dual_Init (C : Cat.{ℓobj ℓhom})
    : Final C = Init (OpCat C)
:= congr_arg Final (eq.symm (OpCat_OpCat C))

/-! #brief A category has an initial object when its opposite has a final obejct.
-/
instance HasFinal.HasInit (C : Cat.{ℓobj ℓhom})
    [C_HasFinal : HasFinal (OpCat C)]
    : HasInit C
:= { init := HasFinal.final (OpCat C) }

/-! #brief A category has a final object when its opposite has an initial obejct.
-/
instance HasInit.HasFinal (C : Cat.{ℓobj ℓhom})
    [C_HasInit : HasInit (OpCat C)]
    : HasFinal C
:= { final := cast (eq.symm (Final_dual_Init C))
                   (HasInit.init (OpCat C))
   }



/- -----------------------------------------------------------------------
Examples of initial and final objects in categories.
----------------------------------------------------------------------- -/

/-! #brief UnitCat has an initial object.
-/
instance UnitCat.HasInit
    : HasInit UnitCat.{ℓobj ℓhom}
:= { init := { obj := punit.star
             , hom := λ c, punit.star
             , hom_uniq := λ c h, begin cases h, trivial end
             }
   }

/-! #brief UnitCat has a final object.
-/
instance UnitCat.HasFinal
    : HasFinal UnitCat.{ℓobj ℓhom}
:= { final := { obj := punit.star
              , hom := λ c, punit.star
              , hom_uniq := λ c h, begin cases h, trivial end
              }
   }


/-! #brief SortCat has an initial object.
-/
instance SortCat.HasInit
    : HasInit SortCat.{ℓ}
:= { init := { obj := pempty
             , hom := λ T e, by cases e
             , hom_uniq := λ c h, funext (λ e, by cases e)
             }
   }

/-! #brief PropCat has an initial object.
-/
instance PropCat.HasInit
    : HasInit PropCat
:= SortCat.HasInit

/-! #brief LeanCat has an initial object.
-/
instance LeanCat.HasInit
    : HasInit LeanCat
:= SortCat.HasInit


/-! #brief SortCat has a final object.
-/
instance SortCat.HasFinal
    : HasFinal SortCat.{ℓ}
:= { final := { obj := punit
              , hom := λ T t, punit.star
              , hom_uniq := λ c h, funext (λ t, begin cases (h t), trivial end)
              }
   }

/-! #brief PropCat has a final object.
-/
instance PropCat.HasFinal
    : HasFinal PropCat
:= SortCat.HasFinal

/-! #brief LeanCat has a final object.
-/
instance LeanCat.HasFinal
    : HasFinal LeanCat
:= SortCat.HasFinal


/-! #brief The category of natural numbers has an initial object.
-/
instance NatCat.HasInitial
    :HasInit NatCat
:= { init := { obj := nat.zero
             , hom := nat.zero_le
             , hom_uniq := λ c h, proof_irrel _ _
             }
   }

end qp
