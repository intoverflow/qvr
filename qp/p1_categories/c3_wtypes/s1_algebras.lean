/- -----------------------------------------------------------------------
Algebras for endofunctors.
----------------------------------------------------------------------- -/

import ..c1_basic
import ..c2_limits

namespace qp

open stdaux

universe variables ℓobj ℓhom



/- -----------------------------------------------------------------------
The category of algebras for an endofunctor.
----------------------------------------------------------------------- -/

/-! #brief An algebra for an endofunctor.
-/
structure EndoAlg {C : Cat.{ℓobj ℓhom}} (F : Fun C C)
    : Type (max ℓobj ℓhom)
:= (carr : C^.obj)
   (hom : C^.hom (F^.obj carr) carr)

/-! #brief Helper for proving equality of EndoAlg.
-/
theorem EndoAlg.eq {C : Cat.{ℓobj ℓhom}} {F : Fun C C}
    : ∀ {X₁ X₂ : EndoAlg F}
        (ωcarr : X₁^.carr = X₂^.carr)
        (ωhom : (X₁^.carr = X₂^.carr) → X₁^.hom == X₂^.hom)
      , X₁ = X₂
| (EndoAlg.mk carr hom₁) (EndoAlg.mk .(carr) hom₂)
  (eq.refl .(carr)) ωhom
:= begin
     assert ωhom' : hom₁ = hom₂,
     { apply eq_of_heq, exact ωhom rfl },
     subst ωhom'
   end

/-! #brief An algebra homomorphism for an endofunctor.
-/
structure EndoAlgHom {C : Cat.{ℓobj ℓhom}} (F : Fun C C)
    (X Y : EndoAlg F)
    : Type (max ℓobj ℓhom)
:= (hom : C^.hom X^.carr Y^.carr)
   (comm : C^.circ Y^.hom (F^.hom hom) = C^.circ hom X^.hom)

/-! #brief Congruence for endo algebra homomorphisms.
-/
theorem EndoAlgHom.congr_hom {C : Cat.{ℓobj ℓhom}} (F : Fun C C)
    {X Y : EndoAlg F}
    : ∀ (h₁ h₂ : EndoAlgHom F X Y)
        (ω : h₁ = h₂)
      , h₁^.hom = h₂^.hom
| h .(h) (eq.refl .(h)) := rfl

/-! #brief A helper for proving two homomorphisms are equal.
-/
theorem EndoAlgHom.eq {C : Cat.{ℓobj ℓhom}} {F : Fun C C}
    {X Y : EndoAlg F}
    : ∀ {F₁ F₂ : EndoAlgHom F X Y}
        (ω : F₁^.hom = F₂^.hom)
      , F₁ = F₂
| (EndoAlgHom.mk hom comm₁) (EndoAlgHom.mk .(hom) comm₂) (eq.refl .(hom))
:= rfl

/-! #brief The identity homomorphism.
-/
definition EndoAlgHom.id {C : Cat.{ℓobj ℓhom}} (F : Fun C C)
    (X : EndoAlg F)
    : EndoAlgHom F X X
:= { hom := C^.id X^.carr
   , comm := by rw [F^.hom_id, C^.circ_id_right, C^.circ_id_left]
   }

/-! #brief The composition of two homomorphisms.
-/
definition EndoAlgHom.comp {C : Cat.{ℓobj ℓhom}} (F : Fun C C)
    {X Y Z : EndoAlg F}
    (g : EndoAlgHom F Y Z)
    (f : EndoAlgHom F X Y)
    : EndoAlgHom F X Z
:= { hom := C^.circ g^.hom f^.hom
   , comm
      := begin
           rw [-C^.circ_assoc, -f^.comm],
           rw [C^.circ_assoc, -g^.comm],
           rw [-C^.circ_assoc, F^.hom_circ]
         end
   }

/-! #brief The category of algebras for an endofunctor.
-/
definition EndoAlgCat {C : Cat.{ℓobj ℓhom}} (F : Fun C C)
    : Cat
:= { obj := EndoAlg F
   , hom := EndoAlgHom F
   , id := EndoAlgHom.id F
   , circ := @EndoAlgHom.comp C F
   , circ_assoc := λ X Y Z W h g f, EndoAlgHom.eq C^.circ_assoc
   , circ_id_left := λ X Y f, EndoAlgHom.eq C^.circ_id_left
   , circ_id_right := λ X Y f, EndoAlgHom.eq C^.circ_id_right
   }

/-! #brief Initial objects in EndoAlgCat are special.
-/
@[class] definition HasInitAlg {C : Cat.{ℓobj ℓhom}} (F : Fun C C)
:= HasInit (EndoAlgCat F)

/-! #brief An initial algebra.
-/
definition initalg {C : Cat.{ℓobj ℓhom}} (F : Fun C C)
    [F_HasInitAlg : HasInitAlg F]
    : EndoAlg F
:= @init _ F_HasInitAlg

/-! #brief The carrier of an initial algebra.
-/
definition initalg.carr {C : Cat.{ℓobj ℓhom}} (F : Fun C C)
    [F_HasInitAlg : HasInitAlg F]
    : C^.obj
:= (initalg F)^.carr

/-! #brief The structure hom of an initial algebra.
-/
definition initalg.hom {C : Cat.{ℓobj ℓhom}} (F : Fun C C)
    [F_HasInitAlg : HasInitAlg F]
    : C^.hom (F^.obj (initalg.carr F)) (initalg.carr F)
:= (initalg F)^.hom

/-! #brief Doubling the initial algebra.
-/
definition initalg.double {C : Cat.{ℓobj ℓhom}} (F : Fun C C)
    [F_HasInitAlg : HasInitAlg F]
    : EndoAlg F
:= { carr := F^.obj (initalg.carr F)
   , hom := F^.hom (initalg.hom F)
   }

/-! #brief The inverse structure hom of an initial algebra.
-/
definition initalg.unhom {C : Cat.{ℓobj ℓhom}} (F : Fun C C)
    [F_HasInitAlg : HasInitAlg F]
    : C^.hom (initalg.carr F) (F^.obj (initalg.carr F))
:= (@init_hom _ F_HasInitAlg (initalg.double F))^.hom

/-! #brief initalg.hom and initalg.unhom are an iso pair.
-/
definition initalg.iso {C : Cat.{ℓobj ℓhom}} (F : Fun C C)
    [F_HasInitAlg : HasInitAlg F]
    : Iso (initalg.hom F) (initalg.unhom F)
:= let φ : EndoAlgHom F (initalg F) (initalg F)
        := { hom := C^.circ (initalg.hom F) (initalg.unhom F)
           , comm := begin
                       repeat { rw -C^.circ_assoc },
                       apply Cat.circ.congr_right,
                       apply eq.trans F^.hom_circ,
                       exact (@init_hom _ F_HasInitAlg (initalg.double F))^.comm
                     end
           }
in let ωφ : φ = EndoAlgHom.id F (initalg F)
         := init_hom.uniq' (EndoAlgCat F)
in let ω : initalg.hom F ∘∘ initalg.unhom F = ⟨⟨initalg.carr F⟩⟩
        := begin
              refine @eq.trans _ _ φ^.hom _ rfl _,
              refine @eq.trans _ _ (EndoAlgHom.id F _)^.hom _ _ rfl,
              rw ωφ
            end
in { id₁ := begin
              apply eq.symm,
              apply eq.trans (eq.symm F^.hom_id),
              refine eq.trans _ (@init_hom _ F_HasInitAlg (initalg.double F))^.comm,
              refine eq.trans _ F^.hom_circ,
              exact congr_arg _ (eq.symm ω),
            end
   , id₂ := ω
   }



/- -----------------------------------------------------------------------
Adámek's theorem.
----------------------------------------------------------------------- -/

/-! #brief Action of the functor used in Adámek's construction on objects.
-/
definition AdamekFun.obj {C : Cat.{ℓobj ℓhom}}
    [C_HasInit : HasInit C]
    (F : Fun C C)
    (n : ℕ)
    : C^.obj
:= (Fun.iter_comp F n)^.obj (init C)

@[simp] theorem AdamekFun.obj.simp {C : Cat.{ℓobj ℓhom}}
    [C_HasInit : HasInit C]
    {F : Fun C C}
    {n : ℕ}
    : AdamekFun.obj F (nat.succ n) = F^.obj (AdamekFun.obj F n)
:= rfl

/-! #brief Action of the functor used in Adámek's construction on homs.
-/
definition AdamekFun.hom {C : Cat.{ℓobj ℓhom}}
    [C_HasInit : HasInit C]
    (F : Fun C C)
    : ∀ (n₁ n₂ : ℕ) (m : ℕ) (ωm : n₂ = m + n₁)
      , C^.hom (AdamekFun.obj F n₁) (AdamekFun.obj F n₂)
| 0 .(m) m (eq.refl .(m)) := init_hom (AdamekFun.obj F m)
| (nat.succ n₁) .(m + nat.succ n₁) m (eq.refl .(m + nat.succ n₁))
:= F^.hom (AdamekFun.hom n₁ (m + n₁) m rfl)

@[simp] theorem AdamekFun.hom.simp {C : Cat.{ℓobj ℓhom}}
    [C_HasInit : HasInit C]
    {F : Fun C C}
    : ∀ {n₁ n₂ : ℕ} {m : ℕ} {ωm : nat.succ n₂ = m + nat.succ n₁}
      , AdamekFun.hom F (nat.succ n₁) (nat.succ n₂) m ωm
         = F^.hom (AdamekFun.hom F n₁ n₂ m (nat.succ.inj ωm))
| 0 .(m) m (eq.refl .(nat.succ m)) := rfl
| (nat.succ n₁) .(m + nat.succ n₁) m (eq.refl .(nat.succ (m + nat.succ n₁)))
:= rfl

/-! #brief Congruence for the Adámek functor on homs.
-/
definition AdamekFun.hcongr_hom {C : Cat.{ℓobj ℓhom}}
    [C_HasInit : HasInit C]
    {F : Fun C C}
    : ∀ {n₁ n₂ : ℕ} {m : ℕ} {ωm : n₂ = m + n₁}
        (p₁ p₂ : ℕ) (q : ℕ)
        (ωnp₁ : n₁ = p₁)
        (ωnp₂ : n₂ = p₂)
        (ωmq : m = q)
      , AdamekFun.hom F n₁ n₂ m ωm
         == AdamekFun.hom F p₁ p₂ q begin subst ωnp₁, subst ωnp₂, subst ωmq, exact ωm end
| n₁ n₂ m ωm .(n₁) .(n₂) .(m)
(eq.refl .(n₁)) (eq.refl .(n₂)) (eq.refl .(m))
:= heq.refl _

/-! #brief Congruence for the Adámek functor on homs.
-/
definition AdamekFun.congr_hom {C : Cat.{ℓobj ℓhom}}
    [C_HasInit : HasInit C]
    {F : Fun C C}
    : ∀ {n₁ n₂ : ℕ} {m : ℕ} {ωm : n₂ = m + n₁}
        (q : ℕ)
        (ωmq : m = q)
      , AdamekFun.hom F n₁ n₂ m ωm
         = AdamekFun.hom F n₁ n₂ q begin subst ωmq, exact ωm end
| n₁ n₂ m ωm .(m) (eq.refl .(m)) := rfl

/-! #brief The functor used in Adámek's construction.
-/
definition AdamekFun {C : Cat.{ℓobj ℓhom}}
    [C_HasInit : HasInit C]
    (F : Fun C C)
    : Fun NatCat C
:= { obj := AdamekFun.obj F
   , hom := λ x y ωxy, AdamekFun.hom F x y (y - x) (eq.symm (nat.sub_add_cancel ωxy))
   , hom_id
      := λ n
         , begin
             dsimp [NatCat] at n,
             induction n with n rec,
             { apply eq.symm, apply init_hom.uniq },
             simp,
             exact eq.trans (Fun.congr_hom rec) F^.hom_id,
           end
   , hom_circ
      := λ x y z g f
         , sorry
   }

/-! #brief Structure hom for the co-cone used in Adámek's construction.
-/
definition Adamek.CoCone.hom {C : Cat.{ℓobj ℓhom}}
    [C_HasInit : HasInit C]
    (F : Fun C C)
    (x : EndoAlg F)
    : ∀ (n : ℕ)
      , C^.hom (AdamekFun.obj F n) x^.carr
| 0 := (init_hom x^.carr)
| (nat.succ n) := C^.circ x^.hom (F^.hom (Adamek.CoCone.hom n))

/-! #brief Commutative property for the co-cone used in Adámek's construction.
-/
definition Adamek.CoCone.comm {C : Cat.{ℓobj ℓhom}}
    [C_HasInit : HasInit C]
    (F : Fun C C)
    (x : EndoAlg F)
    : ∀ {n₁ n₂ : ℕ} (ωn : n₁ ≤ n₂)
      , Adamek.CoCone.hom F x n₁
         = Adamek.CoCone.hom F x n₂
            ∘∘ AdamekFun.hom F n₁ n₂ (n₂ - n₁) (eq.symm (nat.sub_add_cancel ωn))
| 0 n₂ ωn := init_hom.uniq' _
| (nat.succ n₁) 0 ωn := by cases ωn
| (nat.succ n₁) (nat.succ n₂) ωn
:= begin
     dsimp [Adamek.CoCone.hom],
     rw -C^.circ_assoc,
     apply Cat.circ.congr_right,
     simp,
     refine eq.trans _ F^.hom_circ,
     apply Fun.congr_hom,
     apply Adamek.CoCone.comm (nat.le_of_succ_le_succ ωn),
   end

/-! #brief The co-cone used in Adámek's construction.
-/
definition Adamek.CoCone {C : Cat.{ℓobj ℓhom}}
    [C_HasInit : HasInit C]
    (F : Fun C C)
    (x : EndoAlg F)
    : CoCone (AdamekFun F)
:= CoCone.mk
    x^.carr
    (Adamek.CoCone.hom F x)
    (λ n₁ n₂ ωn , Adamek.CoCone.comm F x ωn)


/-! #brief Adámek's construction of initial algebras.
-/
definition Adamek {C : Cat.{ℓobj ℓhom}}
    [C_HasInit : HasInit C]
    (F : Fun C C)
    [Adamek_HasCoLimit : HasCoLimit (AdamekFun F)]
    [F_PresCoLimit : PresCoLimit (AdamekFun F) F]
    : HasInitAlg F
:= HasInit.show
    { carr := colimit (AdamekFun F)
    , hom := let ccone : CoCone (F □□ AdamekFun F)
                      := CoCone.mk
                          (colimit (AdamekFun F))
                          (λ n, colimit.in (AdamekFun F) (nat.succ n))
                          (λ n₁ n₂ ωn, sorry)
             in let f : C^.hom (colimit (F □□ AdamekFun F)) (colimit (AdamekFun F))
                     := colimit.univ ccone
             in f ∘∘ cast_hom (prescolimit (AdamekFun F) F)

    }
    (λ A, { hom := colimit.univ (Adamek.CoCone F A)
          , comm := sorry
          })
    (λ A h
     , EndoAlgHom.eq
        begin
          cases h with h ωh, dsimp at ωh, dsimp,
          apply colimit.univ.uniq (Adamek.CoCone F A),
          intro n, dsimp [Adamek.CoCone, CoCone.mk],
          induction n with n rec,
          { apply init_hom.uniq' },
          { dsimp [Adamek.CoCone.hom],
            rw rec,
            apply eq.trans (Cat.circ.congr_right F^.hom_circ),
            apply eq.trans C^.circ_assoc,
            apply eq.trans (Cat.circ.congr_left ωh),
            rw -C^.circ_assoc,
            apply Cat.circ.congr_right,
            exact sorry
          }
        end)


end qp
