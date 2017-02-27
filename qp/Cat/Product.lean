/- ----------------------------------------------------------------------------
Monoidal categories.
---------------------------------------------------------------------------- -/

import .basic
import .Cone
import .Monoidal
import ..util

namespace qp

universe variables ℓ ℓobj ℓhom



/- ----------------------------------------------------------------------------
Products.
---------------------------------------------------------------------------- -/

/-! #brief Construct a product diagram.
-/
@[reducible] definition ProductDrgm {C : Cat.{ℓobj ℓhom}} {A : Type ℓ}
    (factors : A → [[C]])
    : ObjCat A ⇉⇉ C
:= { obj := factors
   , hom := λ m n f, begin cases f, apply C^.id end
   , hom_id := λ m, rfl
   , hom_circ := λ m n p g f, begin cases f, cases g, dsimp, simp, apply rfl end
   }

/-! #brief A product is a limit of a product diagram.
-/
@[reducible] definition Product {C : Cat.{ℓobj ℓhom}} {A : Type ℓ}
    (factors : A → [[C]])
    : Type (max (ℓ + 1) ℓobj ℓhom)
:= Limit (ProductDrgm factors)

/-! #brief Helper for helper for building products.
-/
@[reducible] definition Product.show_cone {C : Cat.{ℓobj ℓhom}} {A : Type ℓ}
    (factors : A → [[C]])
    (prd : [[C]])
    (π : ∀ (a : A), prd →→ factors a)
    : Cone (ProductDrgm factors)
:= { obj := prd
   , proj := π
   , triangle := λ x₁ x₂ f, begin cases f, dsimp, simp end
   }

/-! #brief Helper for building products.
-/
@[reducible] definition Product.show {C : Cat.{ℓobj ℓhom}} {A : Type ℓ}
    (factors : A → [[C]])
    (prd : [[C]])
    (π : ∀ (a : A), prd →→ factors a)
    (mediate : ∀ (cone : Cone (ProductDrgm factors)), C^.hom cone prd)
    (ωfactors : ∀ (cone : Cone (ProductDrgm factors)) {x : A}, cone^.proj x = π x ∘∘ mediate cone)
    (ωuniq : ∀ (cone : Cone (ProductDrgm factors)) (h : ConeHom cone (Product.show_cone factors prd π)), h^.mediate = mediate cone)
    : Product factors
:= Limit.show (ProductDrgm factors) prd π
    mediate
    (λ x₁ x₂ f, begin cases f, dsimp, simp end)
    @ωfactors
    ωuniq

/-! #brief Helper for defining homs into a product.
-/
@[reducible] definition Product.into {C : Cat.{ℓobj ℓhom}} {A : Type ℓ}
    {factors : A → [[C]]}
    (x : Product factors)
    {c₀ : [[C]]}
    (homs : ∀ (a : A), c₀ →→ factors a)
    : C^.hom c₀ x
:= Limit.mediate x
     { obj := c₀
     , proj := homs
     , triangle := λ x₁ x₂ f, begin cases f, simp end
     }

/-! #brief A category with all products.
-/
@[reducible] definition HasAllProducts (C : Cat.{ℓobj ℓhom})
    : Type (max (ℓ + 1) ℓobj ℓhom)
:= ∀ {A : Type ℓ} (factors : A → [[C]])
   , Product factors

/-! #brief Categories with all limits have all products.
-/
@[reducible] definition HasAllLimits.HasAllProducts {C : Cat.{ℓobj ℓhom}}
    (C_HasAllLimits : HasAllLimits.{ℓ (ℓ + 1) ℓobj ℓhom} C)
    : HasAllProducts.{ℓ ℓobj ℓhom} C
:= λ A factors, C_HasAllLimits (ProductDrgm factors)

/-! #brief Categories with all products have final objects.
-/
@[reducible] definition HasAllProducts.Final {C : Cat.{ℓobj ℓhom}}
    (C_HasAllProducts : HasAllProducts C)
    : Final C
:= let xcone : [[C]] → Cone (ProductDrgm pempty.elim)
            := λ x, { obj := x
                    , proj := λ e, pempty.elim e
                    , triangle := λ e₁ e₂ f, pempty.elim e₁
                    }
   in { obj := (C_HasAllProducts pempty.elim)
      , final := λ x, Limit.mediate (C_HasAllProducts pempty.elim) (xcone x)
      , uniq := λ x h
                , begin
                    apply Limit.mediate_uniq (C_HasAllProducts pempty.elim) (xcone x),
                    intro e, apply pempty.elim e
                  end
      }


/- ----------------------------------------------------------------------------
Finite products.
---------------------------------------------------------------------------- -/

-- A category with all finite products.
structure HasAllFiniteProducts (C : Cat.{ℓobj ℓhom})
    (c₀ : Final C)
    : Type (max 1 ℓobj ℓhom)
:= (prod : ∀ (c₁ c₂ : [[C]]), Product (bool.pick c₁ c₂))
   (prod_id_left₁ : ∀ (c : [[C]]), C^.hom (prod c₀ c) c)
   (prod_id_left₂ : ∀ (c : [[C]]), C^.hom c (prod c₀ c))
   (prod_id_left : ∀ (c : [[C]]), Iso (prod_id_left₁ c) (prod_id_left₂ c))
   (prod_id_right₁ : ∀ (c : [[C]]), C^.hom (prod c c₀) c)
   (prod_id_right₂ : ∀ (c : [[C]]), C^.hom c (prod c c₀))
   (prod_id_right : ∀ (c : [[C]]), Iso (prod_id_right₁ c) (prod_id_right₂ c))

/-! #brief Categories with all products have all finite products.
-/
@[reducible] definition HasAllProducts.HasAllFiniteProducts
    {C : Cat.{ℓobj ℓhom}}
    (C_HasAllProducts : HasAllProducts.{0 ℓobj ℓhom} C)
    : HasAllFiniteProducts C (HasAllProducts.Final @C_HasAllProducts)
:= { prod := λ c₁ c₂, C_HasAllProducts (bool.pick c₁ c₂)
   , prod_id_left₁ := λ c, Limit.proj (C_HasAllProducts (bool.pick (HasAllProducts.Final @C_HasAllProducts) c)) bool.ff
   , prod_id_left₂ := λ c, Product.into (C_HasAllProducts (bool.pick (HasAllProducts.Final @C_HasAllProducts) c))
                            (λ b, begin cases b, exact ⟨⟨c⟩⟩, exact (HasAllProducts.Final @C_HasAllProducts)^.final c, end)
   , prod_id_left := λ c, { id₁ := sorry
                          , id₂ := sorry
                          }
   , prod_id_right₁ := λ c, Limit.proj (C_HasAllProducts (bool.pick c (HasAllProducts.Final @C_HasAllProducts))) bool.tt
   , prod_id_right₂ := λ c, Product.into (C_HasAllProducts (bool.pick c (HasAllProducts.Final @C_HasAllProducts)))
                             (λ b, begin cases b, exact (HasAllProducts.Final @C_HasAllProducts)^.final c, exact ⟨⟨c⟩⟩ end)
   , prod_id_right := λ c, { id₁ := sorry
                           , id₂ := sorry
                           }
   }

/-! #brief A hom into a pair.
-/
@[reducible] definition HasAllFiniteProducts.into {C : Cat.{ℓobj ℓhom}} {c₀ : Final C}
    (C_HasAllFiniteProducts : HasAllFiniteProducts C c₀)
    {c₀ c₁ c₂ : [[C]]}
    (f₁ : c₀ →→ c₁) (f₂ : c₀ →→ c₂)
    : c₀ →→ C_HasAllFiniteProducts^.prod c₁ c₂
:= Product.into (C_HasAllFiniteProducts^.prod c₁ c₂) (λ (b : bool), begin cases b, exact f₂, exact f₁ end)

/-! #brief Projection out of a product.
-/
@[reducible] definition HasAllFiniteProducts.π₁ {C : Cat.{ℓobj ℓhom}} {c₀ : Final C}
    (C_HasAllFiniteProducts : HasAllFiniteProducts C c₀)
    {c₁ c₂ : [[C]]}
    : C^.hom (C_HasAllFiniteProducts^.prod c₁ c₂) c₁
:= Limit.proj (C_HasAllFiniteProducts^.prod c₁ c₂) bool.tt

/-! #brief Projection out of a product.
-/
@[reducible] definition HasAllFiniteProducts.π₂ {C : Cat.{ℓobj ℓhom}} {c₀ : Final C}
    (C_HasAllFiniteProducts : HasAllFiniteProducts C c₀)
    {c₁ c₂ : [[C]]}
    : C^.hom (C_HasAllFiniteProducts^.prod c₁ c₂) c₂
:= Limit.proj (C_HasAllFiniteProducts^.prod c₁ c₂) bool.ff

/-! #brief The pair functor.
-/
@[reducible] definition PairFun {C : Cat.{ℓobj ℓhom}} {c₀ : Final C}
    (C_HasAllFiniteProducts : HasAllFiniteProducts C c₀)
    : C ×× C ⇉⇉ C
:= { obj := λ c, C_HasAllFiniteProducts^.prod c^.fst c^.snd
   , hom := λ c₁ c₂ f, Product.into (C_HasAllFiniteProducts^.prod c₂^.fst c₂^.snd)
                        (λ b, bool.cases_on b
                                (f^.snd ∘∘ Limit.proj (C_HasAllFiniteProducts^.prod (c₁^.fst) (c₁^.snd)) ff)
                                (f^.fst ∘∘ Limit.proj (C_HasAllFiniteProducts^.prod (c₁^.fst) (c₁^.snd)) tt))
   , hom_id := λ c, sorry
   , hom_circ := λ x y z g f, sorry
   }

/-! #brief Braiding the pair functor
-/
@[reducible] definition PairFun.BraidTrans {C : Cat.{ℓobj ℓhom}} {c₀ : Final C}
    (C_HasAllFiniteProducts : HasAllFiniteProducts C c₀)
    : PairFun C_HasAllFiniteProducts
       ↣↣ PairFun C_HasAllFiniteProducts □□ ProdCat.flip
:= { component := λ c, HasAllFiniteProducts.into C_HasAllFiniteProducts
                        (HasAllFiniteProducts.π₂ C_HasAllFiniteProducts)
                        (HasAllFiniteProducts.π₁ C_HasAllFiniteProducts)
   , transport := λ x y f, sorry
   }

/-! #brief Every category with all finite products is a cartesian monoidal category.
-/
@[reducible] definition HasAllFiniteProducts.Monoidal {C : Cat.{ℓobj ℓhom}} {c₀ : Final C}
    (C_HasAllFiniteProducts : HasAllFiniteProducts C c₀)
    : IsMonoidal C (PairFun C_HasAllFiniteProducts) c₀
:= { assoc_left
      := { component := λ xyz, HasAllFiniteProducts.into C_HasAllFiniteProducts
                                (HasAllFiniteProducts.into C_HasAllFiniteProducts
                                  (HasAllFiniteProducts.π₁ C_HasAllFiniteProducts)
                                  (HasAllFiniteProducts.π₁ C_HasAllFiniteProducts ∘∘ HasAllFiniteProducts.π₂ C_HasAllFiniteProducts))
                                (HasAllFiniteProducts.π₂ C_HasAllFiniteProducts ∘∘ HasAllFiniteProducts.π₂ C_HasAllFiniteProducts)
         , transport := λ xyz₁ xyz₂ f, sorry
         }
   , assoc_right
      := { component := λ xyz, HasAllFiniteProducts.into C_HasAllFiniteProducts
                                (HasAllFiniteProducts.π₁ C_HasAllFiniteProducts ∘∘ HasAllFiniteProducts.π₁ C_HasAllFiniteProducts)
                                (HasAllFiniteProducts.into C_HasAllFiniteProducts
                                  (HasAllFiniteProducts.π₂ C_HasAllFiniteProducts ∘∘ HasAllFiniteProducts.π₁ C_HasAllFiniteProducts)
                                  (HasAllFiniteProducts.π₂ C_HasAllFiniteProducts))
         , transport := λ xyz₁ xyz₂ f, sorry
         }
   , assoc_iso :=
      { id₁ := NatTrans.eq
                (λ x, sorry)
      , id₂ := NatTrans.eq
                (λ x, sorry)
      }
   , left_unitor
      := { component := C_HasAllFiniteProducts^.prod_id_left₁
         , transport := λ x y f, begin exact sorry end
         }
   , left_unitor_inv
      := { component := C_HasAllFiniteProducts^.prod_id_left₂
         , transport := begin exact sorry end
         }
   , left_unitor_iso := { id₁ := begin apply NatTrans.eq, intro c, apply (C_HasAllFiniteProducts^.prod_id_left c)^.id₁ end
                        , id₂ := begin apply NatTrans.eq, intro c, apply (C_HasAllFiniteProducts^.prod_id_left c)^.id₂ end
                        }
   , right_unitor
      := { component := C_HasAllFiniteProducts^.prod_id_right₁
         , transport := begin exact sorry end
         }
   , right_unitor_inv
      := { component := C_HasAllFiniteProducts^.prod_id_right₂
         , transport := begin exact sorry end
         }
   , right_unitor_iso := { id₁ := begin apply NatTrans.eq, intro c, apply (C_HasAllFiniteProducts^.prod_id_right c)^.id₁ end
                         , id₂ := begin apply NatTrans.eq, intro c, apply (C_HasAllFiniteProducts^.prod_id_right c)^.id₂ end
                         }
   , triangle := begin exact sorry end
   , pentagon := begin exact sorry end
   }

/-! #brief Cartesian monoidal categories are symmetric.
-/
theorem HasAllFiniteProducts.Symmetric {C : Cat.{ℓobj ℓhom}} {c₀ : Final C}
    (C_HasAllFiniteProducts : HasAllFiniteProducts C c₀)
    : IsSymmetric C
        (HasAllFiniteProducts.Monoidal @C_HasAllFiniteProducts)
        (PairFun.BraidTrans @C_HasAllFiniteProducts)
:= IsSymmetric.show
    { id₁ := begin apply NatTrans.eq, intro c, cases c with c₁ c₂, exact sorry end
    , id₂ := begin apply NatTrans.eq, intro c, cases c with c₁ c₂, exact sorry end
    }
    (λ x y z, begin
                exact sorry
              end)

end qp
