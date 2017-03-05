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
Product diagrams.
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



/- ----------------------------------------------------------------------------
Products.
---------------------------------------------------------------------------- -/

/-! #brief A product is a limit of a product diagram.
-/
@[reducible] definition Product {C : Cat.{ℓobj ℓhom}} {A : Type ℓ}
    (factors : A → [[C]])
    : Type (max (ℓ + 1) ℓobj ℓhom)
:= Limit (ProductDrgm factors)

/-! #brief Helper for helper for building products.
-/
@[reducible] definition Product.mk_cone {C : Cat.{ℓobj ℓhom}} {A : Type ℓ}
    (factors : A → [[C]])
    (prd : [[C]])
    (π : ∀ (a : A), prd →→ factors a)
    : Cone (ProductDrgm factors)
:= { obj := prd
   , hom := π
   , triangle := λ x₁ x₂ f, begin cases f, dsimp, simp end
   }

/-! #brief Helper for building products.
-/
@[reducible] definition Product.show {C : Cat.{ℓobj ℓhom}} {A : Type ℓ}
    (factors : A → [[C]])
    (prd : [[C]])
    (π : ∀ (a : A), prd →→ factors a)
    (into : ∀ (cone : Cone (ProductDrgm factors)), C^.hom cone prd)
    (ωfactors : ∀ (cone : Cone (ProductDrgm factors)) {x : A}, cone^.hom x = π x ∘∘ into cone)
    (ωuniq : ∀ (cone : Cone (ProductDrgm factors)) (h : ConeHom cone (Product.mk_cone factors prd π)), h^.mediate = into cone)
    : Product factors
:= Limit.mk (ProductDrgm factors) prd π
    into
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
:= Limit.univ x (Product.mk_cone factors c₀ homs)

-- TODO:
-- Product.proj
-- Product.into.factor
-- Product.into.uniq



/- ----------------------------------------------------------------------------
Categories with products.
---------------------------------------------------------------------------- -/

/-! #brief A category with all products.
-/
class HasAllProducts (C : Cat.{ℓobj ℓhom})
    : Type (max (ℓ + 1) ℓobj ℓhom)
:= {product : ∀ {A : Type ℓ} (factors : A → [[C]])
              , Product factors
   }

/-! #brief A product in a category with all products.
-/
definition product {C : Cat.{ℓobj ℓhom}}
    [C_HasAllProducts : HasAllProducts.{ℓ} C]
    {A : Type ℓ}
    (factors : A → [[C]])
    : Product factors
:= HasAllProducts.product factors

/-! #brief Categories with all limits have all products.
-/
instance HasAllLimits.HasAllProducts {C : Cat.{ℓobj ℓhom}}
    [C_HasAllLimits : HasAllLimits.{ℓ (ℓ + 1) ℓobj ℓhom} C]
    : HasAllProducts.{ℓ ℓobj ℓhom} C
:= @HasAllProducts.mk C (λ A factors, limit (ProductDrgm factors))

/-! #brief Categories with all products have final objects.
-/
instance HasAllProducts.HasFinal {C : Cat.{ℓobj ℓhom}}
    [C_HasAllProducts : HasAllProducts C]
    : HasFinal C
:= let xcone : [[C]] → Cone (ProductDrgm pempty.elim)
            := λ x, { obj := x
                    , hom := λ e, pempty.elim e
                    , triangle := λ e₁ e₂ f, pempty.elim e₁
                    }
   in { final := { obj := product (@pempty.elim [[C]])
                 , hom := λ x, Limit.univ (product pempty.elim) (xcone x)
                 , uniq := λ x h
                           , begin
                               apply Limit.univ.uniq (product pempty.elim) (xcone x),
                               intro e, apply pempty.elim e
                             end
                 }
      }



/- ----------------------------------------------------------------------------
Finite products.
---------------------------------------------------------------------------- -/

-- A category with all finite products.
class HasAllFiniteProducts (C : Cat.{ℓobj ℓhom})
    : Type (max 1 ℓobj ℓhom)
:= (prod : ∀ [C_HasFinal : HasFinal C] (c₁ c₂ : [[C]])
           , Product (bool.pick c₁ c₂))
   (prod_id_left₁ : ∀ [C_HasFinal : HasFinal C] (c : [[C]])
                    , C^.hom (prod (final C) c) c)
   (prod_id_left₂ : ∀ [C_HasFinal : HasFinal C] (c : [[C]])
                    , C^.hom c (prod (final C) c))
   (prod_id_left : ∀ [C_HasFinal : HasFinal C] (c : [[C]])
                   , Iso (prod_id_left₁ c) (prod_id_left₂ c))
   (prod_id_right₁ : ∀ [C_HasFinal : HasFinal C] (c : [[C]])
                     , C^.hom (prod c (final C)) c)
   (prod_id_right₂ : ∀ [C_HasFinal : HasFinal C] (c : [[C]])
                     , C^.hom c (prod c (final C)))
   (prod_id_right : ∀ [C_HasFinal : HasFinal C] (c : [[C]])
                    , Iso (prod_id_right₁ c) (prod_id_right₂ c))

/-! #brief A finite product in a category with all finite products.
-/
definition fin_product {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    [C_HasAllFiniteProducts : HasAllFiniteProducts C]
    (c₁ c₂ : [[C]])
    : Product (bool.pick c₁ c₂)
:= HasAllFiniteProducts.prod c₁ c₂

-- /-! #brief Categories with all products have all finite products.
-- -/
-- @[reducible] definition HasAllProducts.HasAllFiniteProducts
--     {C : Cat.{ℓobj ℓhom}}
--     [C_HasAllProducts : HasAllProducts.{0 ℓobj ℓhom} C]
--     : HasAllFiniteProducts C
-- := { prod := λ c₁ c₂, product (bool.pick c₁ c₂)
--    , prod_id_left₁ := λ c, Limit.proj (product (bool.pick (final C) c)) bool.ff
--    , prod_id_left₂ := λ c, Product.into (product (bool.pick (final C) c))
--                             (λ b, begin cases b, exact ⟨⟨c⟩⟩, exact final_hom, end)
--    , prod_id_left := λ c, { id₁ := sorry
--                           , id₂ := sorry
--                           }
--    , prod_id_right₁ := λ c, Limit.proj (product (bool.pick c (final C))) bool.tt
--    , prod_id_right₂ := λ c, Product.into (product (bool.pick c (final C)))
--                              (λ b, begin cases b, exact final_hom, exact ⟨⟨c⟩⟩ end)
--    , prod_id_right := λ c, { id₁ := sorry
--                            , id₂ := sorry
--                            }
--    }

/-! #brief A hom into a pair.
-/
@[reducible] definition fin_product.into {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    [C_HasAllFiniteProducts : HasAllFiniteProducts C]
    {c₀ c₁ c₂ : [[C]]}
    (f₁ : c₀ →→ c₁) (f₂ : c₀ →→ c₂)
    : c₀ →→ fin_product c₁ c₂
:= Product.into (fin_product c₁ c₂) (λ (b : bool), begin cases b, exact f₂, exact f₁ end)

/-! #brief Left-projection out of a finite product.
-/
@[reducible] definition fin_product.π₁ {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    [C_HasAllFiniteProducts : HasAllFiniteProducts C]
    {c₁ c₂ : [[C]]}
    : C^.hom (fin_product c₁ c₂) c₁
:= Limit.proj (fin_product c₁ c₂) bool.tt

/-! #brief Right-projection out of a product.
-/
@[reducible] definition fin_product.π₂ {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    [C_HasAllFiniteProducts : HasAllFiniteProducts C]
    {c₁ c₂ : [[C]]}
    : C^.hom (fin_product c₁ c₂) c₂
:= Limit.proj (fin_product c₁ c₂) bool.ff



/- ----------------------------------------------------------------------------
The pair functor.
---------------------------------------------------------------------------- -/

/-! #brief The pair functor.
-/
@[reducible] definition PairFun (C : Cat.{ℓobj ℓhom})
    [C_HasFinal : HasFinal C]
    [C_HasAllFiniteProducts : HasAllFiniteProducts C]
    : C ×× C ⇉⇉ C
:= { obj := λ c, fin_product c^.fst c^.snd
   , hom := λ c₁ c₂ f, Product.into (fin_product c₂^.fst c₂^.snd)
                        (λ b, bool.cases_on b
                                (f^.snd ∘∘ Limit.proj (fin_product (c₁^.fst) (c₁^.snd)) ff)
                                (f^.fst ∘∘ Limit.proj (fin_product (c₁^.fst) (c₁^.snd)) tt))
   , hom_id := λ c, sorry
   , hom_circ := λ x y z g f, sorry
   }

/-! #brief Braiding the pair functor
-/
@[reducible] definition PairFun.BraidTrans {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    [C_HasAllFiniteProducts : HasAllFiniteProducts C]
    : PairFun C ↣↣ PairFun C □□ ProdCat.flip
:= { component := λ c, fin_product.into fin_product.π₂ fin_product.π₁
   , transport := λ x y f, sorry
   }

/-! #brief Every category with all finite products is a cartesian monoidal category.
-/
@[reducible] definition HasAllFiniteProducts.Monoidal {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    [C_HasAllFiniteProducts : HasAllFiniteProducts C]
    : IsMonoidal C (PairFun C) (final C)
:= { assoc_left
      := { component := λ xyz, fin_product.into
                                (fin_product.into fin_product.π₁ (fin_product.π₁ ∘∘ fin_product.π₂))
                                (fin_product.π₂ ∘∘ fin_product.π₂)
         , transport := λ xyz₁ xyz₂ f, sorry
         }
   , assoc_right
      := { component := λ xyz, fin_product.into
                                (fin_product.π₁ ∘∘ fin_product.π₁)
                                (fin_product.into
                                  (fin_product.π₂ ∘∘ fin_product.π₁)
                                  (fin_product.π₂))
         , transport := λ xyz₁ xyz₂ f, sorry
         }
   , assoc_iso :=
      { id₁ := NatTrans.eq
                (λ x, sorry)
      , id₂ := NatTrans.eq
                (λ x, sorry)
      }
   , left_unitor
      := { component := HasAllFiniteProducts.prod_id_left₁
         , transport := λ x y f, begin exact sorry end
         }
   , left_unitor_inv
      := { component := HasAllFiniteProducts.prod_id_left₂
         , transport := begin exact sorry end
         }
   , left_unitor_iso := { id₁ := begin apply NatTrans.eq, intro c, apply (HasAllFiniteProducts.prod_id_left c)^.id₁ end
                        , id₂ := begin apply NatTrans.eq, intro c, apply (HasAllFiniteProducts.prod_id_left c)^.id₂ end
                        }
   , right_unitor
      := { component := HasAllFiniteProducts.prod_id_right₁
         , transport := begin exact sorry end
         }
   , right_unitor_inv
      := { component := HasAllFiniteProducts.prod_id_right₂
         , transport := begin exact sorry end
         }
   , right_unitor_iso := { id₁ := begin apply NatTrans.eq, intro c, apply (HasAllFiniteProducts.prod_id_right c)^.id₁ end
                         , id₂ := begin apply NatTrans.eq, intro c, apply (HasAllFiniteProducts.prod_id_right c)^.id₂ end
                         }
   , triangle := begin exact sorry end
   , pentagon := begin exact sorry end
   }

/-! #brief Cartesian monoidal categories are symmetric.
-/
theorem HasAllFiniteProducts.Symmetric {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    [C_HasAllFiniteProducts : HasAllFiniteProducts C]
    : IsSymmetric C
        HasAllFiniteProducts.Monoidal
        PairFun.BraidTrans
:= IsSymmetric.show
    { id₁ := begin apply NatTrans.eq, intro c, cases c with c₁ c₂, exact sorry end
    , id₂ := begin apply NatTrans.eq, intro c, cases c with c₁ c₂, exact sorry end
    }
    (λ x y z, begin
                exact sorry
              end)

end qp
