/- ----------------------------------------------------------------------------
Monoidal categories.
---------------------------------------------------------------------------- -/

import .basic
import .Cone
import ..util

namespace qp

universe variables ℓ ℓobj ℓhom



/-! #brief Construct a product diagram.
-/
@[reducible] definition ProductDrgm {C : Cat.{(ℓobj + 1) ℓhom}} {A : Sort ℓ}
    (factors : A → [[C]])
    : ObjCat A ⇉⇉ C
:= { obj := factors
   , hom := λ m n f, begin cases f, apply C^.id end
   , hom_id := λ m, rfl
   , hom_circ
      := λ m n p g f, begin exact sorry end
   }

/-! #brief A product is a limit of a finite product diagram.
-/
@[reducible] definition IsProduct {C : Cat.{(ℓobj + 1) ℓhom}} {A : Sort ℓ}
    (factors : A → [[C]])
    (x : [[C]])
    : Type (max 1 ℓ (ℓobj + 1) ℓhom)
:= IsLimit (ProductDrgm factors) x

/-! #brief Helper for defining homs into a product.
-/
@[reducible] definition IsProduct.into {C : Cat.{(ℓobj + 1) ℓhom}} {A : Sort ℓ}
    {c₀ x : [[C]]}
    {factors : A → [[C]]}
    (x_IsProduct : IsProduct factors x)
    (homs : ∀ (a : A), c₀ →→ factors a)
    : c₀ →→ x
:= IsLimit.mediate x_IsProduct
     { proj := homs
     , triangle := λ x₁ x₂ f, begin cases f, simp end
     }

-- A category with all products.
structure HasAllProducts (C : Cat.{(ℓobj + 1) ℓhom})
    : Type (max 1 ℓ (ℓobj + 1) ℓhom)
:= (prod : ∀ {A : Sort ℓ}, (A → [[C]]) → [[C]])
   (is_prod : ∀ {A : Sort ℓ} (factors : A → [[C]])
              , IsProduct factors (prod factors))

-- A category with all finite products.
structure HasAllFiniteProducts (C : Cat.{(ℓobj + 1) ℓhom})
    : Type (max 1 (ℓobj + 1) ℓhom)
:= (prod : list [[C]] → [[C]])
   (is_prod : ∀ (factors : list [[C]])
              , IsProduct (list.get factors) (prod factors))

/-! #brief Flattening of products.
-/
definition HasAllFiniteProducts.flat_limit {C : Cat.{(ℓobj + 1) ℓhom}}
    (C_HasAllFiniteProducts : HasAllFiniteProducts C)
    (factors₁ factors₂ factors₃ : list [[C]])
    : IsProduct (list.get (factors₁ ++ factors₂ ++ factors₃))
                (C_HasAllFiniteProducts^.prod (factors₁ ++ [C_HasAllFiniteProducts^.prod factors₂] ++ factors₃))
:= { is_cone
      := { proj
            := λ n
               , let lim := C_HasAllFiniteProducts^.is_prod (factors₁ ++ [C_HasAllFiniteProducts^.prod factors₂] ++ factors₃)
                 in if ω₁ : n^.val < list.length factors₁
                     then cast sorry (IsLimit.proj lim { val := n^.val, is_lt := sorry })
                     else if ω₂ : n^.val < list.length factors₁ + list.length factors₂
                           then let foo₁ : C_HasAllFiniteProducts^.prod (factors₁ ++ [C_HasAllFiniteProducts^.prod factors₂] ++ factors₃) →→ C_HasAllFiniteProducts^.prod factors₂
                                 := cast sorry (IsLimit.proj lim { val := list.length factors₁, is_lt := sorry }) in
                                let foo₂ : C_HasAllFiniteProducts^.prod factors₂ →→ list.get (factors₁ ++ factors₂ ++ factors₃) n
                                 := cast sorry (IsLimit.proj (C_HasAllFiniteProducts^.is_prod factors₂) { val := n^.val - list.length factors₁, is_lt := sorry })
                                in foo₂ ∘∘ foo₁
                           else cast sorry (IsLimit.proj lim { val := n^.val - list.length factors₂ + 1, is_lt := sorry })
         , triangle
            := λ n₁ n₂ f, begin cases f, simp end
         }
   , is_final
      := { final := sorry
         , uniq := sorry
         }
   }

/-! #brief The flattening hom.
-/
definition HasAllFiniteProducts.flatten {C : Cat.{(ℓobj + 1) ℓhom}}
    (C_HasAllFiniteProducts : HasAllFiniteProducts C)
    (factors₁ factors₂ factors₃ : list [[C]])
    : C_HasAllFiniteProducts^.prod (factors₁ ++ [C_HasAllFiniteProducts^.prod factors₂] ++ factors₃)
       →→ C_HasAllFiniteProducts^.prod (factors₁ ++ factors₂ ++ factors₃)
:= IsLimit.mediate (C_HasAllFiniteProducts^.is_prod (factors₁ ++ factors₂ ++ factors₃))
    (HasAllFiniteProducts.flat_limit C_HasAllFiniteProducts factors₁ factors₂ factors₃)^.is_cone

/-! #brief The exploding hom.
-/
definition HasAllFiniteProducts.explode {C : Cat.{(ℓobj + 1) ℓhom}}
    (C_HasAllFiniteProducts : HasAllFiniteProducts C)
    (factors₁ factors₂ factors₃ : list [[C]])
    : C_HasAllFiniteProducts^.prod (factors₁ ++ factors₂ ++ factors₃)
       →→ C_HasAllFiniteProducts^.prod (factors₁ ++ [C_HasAllFiniteProducts^.prod factors₂] ++ factors₃)
:= IsLimit.mediate (HasAllFiniteProducts.flat_limit C_HasAllFiniteProducts factors₁ factors₂ factors₃)
     ((C_HasAllFiniteProducts^.is_prod (factors₁ ++ factors₂ ++ factors₃))^.is_cone)

/-! #brief Explosion and flattening of products are isomorphisms.
-/
@[reducible] definition HasAllFiniteProducts.flatten_explode_iso {C : Cat.{(ℓobj + 1) ℓhom}}
    (C_HasAllFiniteProducts : HasAllFiniteProducts C)
    (factors₁ factors₂ factors₃ : list [[C]])
    : Iso (HasAllFiniteProducts.flatten C_HasAllFiniteProducts factors₁ factors₂ factors₃)
          (HasAllFiniteProducts.explode C_HasAllFiniteProducts factors₁ factors₂ factors₃)
:= IsLimit.iso (HasAllFiniteProducts.flat_limit C_HasAllFiniteProducts factors₁ factors₂ factors₃)
                          (C_HasAllFiniteProducts^.is_prod (factors₁ ++ factors₂ ++ factors₃))

/-! #brief Helper for the pairwise product functor.
-/
@[reducible] definition HasAllFiniteProducts.PairFun₁ {C : Cat.{(ℓobj + 1) ℓhom}}
    {xy₁ xy₂ : [[C ×× C]]}
    (f : (C ×× C)^.hom xy₁ xy₂)
    : ∀ (n : fin 2)
      , ProductDrgm (list.get [xy₁^.fst, xy₁^.snd]) n →→ ProductDrgm (list.get [xy₂^.fst, xy₂^.snd]) n
| (fin.mk 0 ω) := f^.fst
| (fin.mk 1 ω) := f^.snd
| (fin.mk (nat.succ (nat.succ n)) ω) := false.cases_on _ begin cases ω, cases a, cases a end

/-! #brief The pairwise product functor.
-/
@[reducible] definition HasAllFiniteProducts.PairFun {C : Cat.{(ℓobj + 1) ℓhom}}
    (C_HasAllFiniteProducts : HasAllFiniteProducts C)
    : C ×× C ⇉⇉ C
:= { obj := λ xy, C_HasAllFiniteProducts^.prod [xy^.fst, xy^.snd]
   , hom
      := λ xy₁ xy₂ f
         , IsLimit.mediate (C_HasAllFiniteProducts^.is_prod [xy₂^.fst, xy₂^.snd])
            { proj := λ n, HasAllFiniteProducts.PairFun₁ f n
                            ∘∘ IsLimit.proj (C_HasAllFiniteProducts^.is_prod [xy₁^.fst, xy₁^.snd]) n
            , triangle := λ z₁ z₂ g, begin cases g, simp end
            }
   , hom_id
      := λ xy
         , begin
             apply eq.symm, apply IsLimit.mediate_uniq, simp,
             intro n,
             cases n with n ωn,
             cases n with n, { apply Cat.circ_id_left },
             cases n with n, { apply Cat.circ_id_left },
             cases ωn, cases a, cases a
           end
   , hom_circ := begin exact sorry end
   }

/-! #brief Categories with finite products have final objects.
-/
@[reducible] definition HasAllFiniteProducts.Final {C : Cat.{(ℓobj + 1) ℓhom}}
    (C_HasAllFiniteProducts : HasAllFiniteProducts C)
    : IsFinal C (C_HasAllFiniteProducts^.prod [])
:= { final := λ c, IsLimit.mediate (C_HasAllFiniteProducts^.is_prod [])
                    { proj := λ n, fin.zero_elim n
                    , triangle := λ x₁ x₂ f, fin.zero_elim x₁
                    }
   , uniq := λ c h, begin apply IsLimit.mediate_uniq, intro x, exact fin.zero_elim x end
   }

/-! #brief Categories with all finite limits have all finite products.
-/
@[reducible] definition HasAllFiniteLimits.HasAllFiniteProducts {C : Cat.{(ℓobj + 1) ℓhom}}
    (C_HasAllFiniteLimits : HasAllFiniteLimits C)
    : HasAllFiniteProducts C
:= { prod
      := λ factors
         , C_HasAllFiniteLimits^.limit (ObjCat.Fin (fin.FinType (list.length factors)))
            (ProductDrgm (list.get factors))
   , is_prod
      := λ factors
         , C_HasAllFiniteLimits^.is_limit (ObjCat.Fin (fin.FinType (list.length factors)))
            (ProductDrgm (list.get factors))
   }

end qp
