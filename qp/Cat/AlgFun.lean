/- ----------------------------------------------------------------------------
Algebras of endo-functors.
---------------------------------------------------------------------------- -/

import .basic
import .Cone
import .Fun

universe variables ℓobj ℓhom

namespace qp



/- ----------------------------------------------------------------------------
Algebras of endo-functors.
---------------------------------------------------------------------------- -/

-- An algebra of an endofunctor.
structure AlgFun {C : Cat.{ℓobj ℓhom}} (F : C ⇉⇉ C)
    : Type (max ℓobj ℓhom)
:= (obj : [[C]])
   (carrier : F obj →→ obj)

-- An hom of an algebra of an endofunctor.
structure AlgFunHom {C : Cat.{ℓobj ℓhom}} {F : C ⇉⇉ C}
    (X Y : AlgFun F)
    : Type (max ℓobj ℓhom)
:= (hom : X^.obj →→ Y^.obj)
   (square : hom ∘∘ X^.carrier = Y^.carrier ∘∘ (F^.hom hom))

/-! #brief An helper for proving equality of algebra homs.
-/
theorem AlgFunHom.eq {C : Cat.{ℓobj ℓhom}} {F : C ⇉⇉ C}
    {X Y : AlgFun F}
    : ∀ {f₁ f₂ : AlgFunHom X Y}
      , f₁^.hom = f₂^.hom
      → f₁ = f₂
| (AlgFunHom.mk f ω₁) (AlgFunHom.mk .f ω₂) (eq.refl .f) := rfl

/-! #brief The identity algebra hom.
-/
@[reducible] definition AlgFunHom.id {C : Cat.{ℓobj ℓhom}} {F : C ⇉⇉ C}
    (X : AlgFun F)
    : AlgFunHom X X
:= { hom := ⟨⟨X^.obj⟩⟩
   , square := by simp
   }

/-! #brief Composition of algebra homs.
-/
@[reducible] definition AlgFunHom.comp {C : Cat.{ℓobj ℓhom}} {F : C ⇉⇉ C}
    {X Y Z : AlgFun F} (g : AlgFunHom Y Z) (f : AlgFunHom X Y)
    : AlgFunHom X Z
:= { hom := g^.hom ∘∘ f^.hom
   , square := begin
                 rw -C^.circ_assoc,
                 rw f^.square,
                 rw C^.circ_assoc,
                 rw g^.square,
                 rw F^.hom_circ,
                 rw C^.circ_assoc
               end
   }

/-! #brief The category of algebras of an endofunctor.
-/
@[reducible] definition AlgFunCat {C : Cat.{ℓobj ℓhom}}
    (F : C ⇉⇉ C)
    : Cat.{(max ℓobj ℓhom) ((max ℓobj ℓhom) + 1)}
:= { obj := AlgFun F
   , hom := AlgFunHom
   , id := @AlgFunHom.id C F
   , circ := @AlgFunHom.comp C F
   , circ_assoc := λ x y z w h g f, begin apply AlgFunHom.eq, apply C^.circ_assoc end
   , circ_id_left := λ x y f, begin apply AlgFunHom.eq, simp end
   , circ_id_right := λ x y f, begin apply AlgFunHom.eq, simp end
   }



/- ----------------------------------------------------------------------------
Initial algebras of endo-functors.
---------------------------------------------------------------------------- -/

/-! #brief Action of the functor used in Adámek's construction on objects.
-/
definition AdamekFun.obj {C : Cat.{ℓobj ℓhom}}
    [C_HasInit : HasInit C]
    (F : C ⇉⇉ C)
    (n : ℕ)
    : [[C]]
:= Fun.iter_comp F n (init C)

@[simp] theorem AdamekFun.obj.succ {C : Cat.{ℓobj ℓhom}}
    [C_HasInit : HasInit C]
    {F : C ⇉⇉ C}
    {n : ℕ}
    : AdamekFun.obj F (nat.succ n) = F (AdamekFun.obj F n)
:= rfl

/-! #brief Action of the functor used in Adámek's construction on homs.
-/
definition AdamekFun.hom {C : Cat.{ℓobj ℓhom}}
    [C_HasInit : HasInit C]
    (F : C ⇉⇉ C)
    : ∀ (n₁ n₂ : ℕ) (m : ℕ) (ωm : n₂ = m + n₁)
      , AdamekFun.obj F n₁ →→ AdamekFun.obj F n₂
| 0 .m m (eq.refl .m) := init_hom
| (nat.succ n₁) .(m + nat.succ n₁) m (eq.refl .(m + nat.succ n₁))
:= F ↗ AdamekFun.hom n₁ (m + n₁) m rfl

/-! #brief The functor used in Adámek's construction.
-/
definition AdamekFun {C : Cat.{ℓobj ℓhom}}
    [C_HasInit : HasInit C]
    (F : C ⇉⇉ C)
    : NatCat ⇉⇉ C
:= { obj := AdamekFun.obj F
   , hom := λ x y f, AdamekFun.hom F x y f^.elt_of f^.has_property
   , hom_id
      := λ n
         , begin
             dsimp [NatCat] at n,
             induction n with n,
             { apply eq.symm, apply init_hom.uniq },
             { have ω₁ : nat.succ n = 0 + nat.succ n,
               { exact sorry },
               have ω₂ : n = 0 + n,
               { exact sorry },
               calc AdamekFun.hom F (nat.succ n) (nat.succ n) 0 ω₁
                        = F ↗ (AdamekFun.hom F n n 0 ω₂)           : sorry
                    ... = F ↗ ⟨⟨AdamekFun.obj F n⟩⟩                : sorry -- by rw ih_1
                    ... = ⟨⟨AdamekFun.obj F (nat.succ n)⟩⟩         : F^.hom_id
             }
           end
   , hom_circ
      := λ x y z g f
         , sorry
   }

/-! #brief The co-cone used in Adámek's construction.
-/
definition Adamek.CoCone {C : Cat.{ℓobj ℓhom}}
    [C_HasInit : HasInit C]
    (F : C ⇉⇉ C)
    [Adamek_HasCoLimit : HasCoLimit (AdamekFun F)]
    [F_Preserves : PreservesCoLimit F (AdamekFun F)]
    x : [[{{AlgFunCat F}}⁻¹]]
    : Cone (OpFun (AdamekFun F))
:= { obj := x^.obj
   , hom := λ n, nat.rec_on n
                   init_hom
                   (λ n rec, x^.carrier ∘∘ (F ↗ rec))
   , triangle
      := λ n₁ n₂ f
         , begin
             dsimp [NatCat] at n₁,
             dsimp [NatCat] at n₂,
             cases f with m ωm,
             assert ωm' : n₁ = n₂ + m, { subst ωm, apply nat.add_comm },
             subst ωm',
             induction m with m,
             { dsimp [OpCat, OpFun],
               refine eq.trans (eq.symm C^.circ_id_right) _,
               exact sorry -- true, but there's casting problems.
             },
             { rw (ih_1 (nat.add_comm n₂ m)),
               dsimp [OpCat, OpFun, AdamekFun],
               exact sorry -- true, but there's casting problems.
             }
           end
   }

/-! #brief Adámek's construction.

Note that the class requirements are easy to satisfiy:
* HasAllCoLimitsOfShape C NatCat        implies     HasCoLimit (AdamekFun F)
* PreservesCoLimitsOfShape F NatCat     implies     PreservesCoLimit F (AdamekFun F)

-/
definition Adamek {C : Cat.{ℓobj ℓhom}}
    [C_HasInit : HasInit C]
    (F : C ⇉⇉ C)
    [Adamek_HasCoLimit : HasCoLimit (AdamekFun F)]
    [F_Preserves : PreservesCoLimit F (AdamekFun F)]
    : Init (AlgFunCat F)
:= { obj := { obj := ↑(colimit (AdamekFun F))
            , carrier
               := let f₂ : ↑(colimit (F □□ AdamekFun F)) →→ ↑(colimit (AdamekFun F))
                        := colimit.univ (F □□ AdamekFun F)
                            { obj := ↑(colimit (AdamekFun F))
                            , hom := λ n₁, CoLimit.incl (colimit (AdamekFun F)) (nat.succ n₁)
                            , triangle := λ n₁ n₂ f, sorry
                            }
               in let f₁ : F ↑(colimit (AdamekFun F)) →→ ↑(colimit (F □□ AdamekFun F))
                        := colimit.preserves.out F (AdamekFun F)
               in f₂ ∘∘ f₁
            }
   , hom := λ x, { hom := colimit.univ (AdamekFun F) (Adamek.CoCone F x)
                 , square := sorry
                 }
   , uniq := λ x h, begin apply AlgFunHom.eq, dsimp, dsimp at h, exact sorry end
   }

end qp
