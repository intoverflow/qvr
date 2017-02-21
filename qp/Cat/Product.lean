/- ----------------------------------------------------------------------------
Monoidal categories.
---------------------------------------------------------------------------- -/

import .basic
import .Cone
import ..util

namespace qp

universe variables ℓobj ℓhom



/-! #brief Construct a finite product diagram.
-/
@[reducible] definition FiniteProductDrgm {C : Cat.{(ℓobj + 1) ℓhom}}
    (factors : list [[C]])
    : ObjCat (fin (list.length factors)) ⇉⇉ C
:= { obj := λ m, list.get factors m
   , hom := λ m n f, begin cases f, apply C^.id end
   , hom_id := λ m, rfl
   , hom_circ
      := λ m n p g f, begin exact sorry end
   }

/-! #brief A finite product is a limit of a finite product diagram.
-/
@[reducible] definition IsFiniteProduct {C : Cat.{(ℓobj + 1) ℓhom}}
    (factors : list [[C]])
    (x : [[C]])
    : Type (max 1 (ℓobj + 1) ℓhom)
:= IsLimit (FiniteProductDrgm factors) x

/-! #brief Helper for defining homs into a product.
-/
@[reducible] definition IsFiniteProduct.into {C : Cat.{(ℓobj + 1) ℓhom}}
    {c₀ x : [[C]]}
    {factors : list [[C]]}
    (x_IsFiniteProduct : IsFiniteProduct factors x)
    (homs : ∀ (n : fin (list.length factors)), c₀ →→ list.get factors n)
    : c₀ →→ x
:= IsLimit.mediate x_IsFiniteProduct
     { proj := homs
     , triangle := λ x₁ x₂ f, begin cases f, simp end
     }

-- A category with all finite products.
structure HasAllFiniteProducts (C : Cat.{(ℓobj + 1) ℓhom})
    : Type (max 1 (ℓobj + 1) ℓhom)
:= (prod : list [[C]] → [[C]])
   (is_prod : ∀ (factors : list [[C]])
              , IsFiniteProduct factors (prod factors))

/-! #brief Flattening of products.
-/
definition HasAllFiniteProducts.flatten {C : Cat.{(ℓobj + 1) ℓhom}}
    (C_HasAllFiniteProducts : HasAllFiniteProducts C)
    (factors₁ factors₂ factors₃ : list [[C]])
    : C_HasAllFiniteProducts^.prod (factors₁ ++ [C_HasAllFiniteProducts^.prod factors₂] ++ factors₃)
       →→ C_HasAllFiniteProducts^.prod (factors₁ ++ factors₂ ++ factors₃)
:= IsFiniteProduct.into (C_HasAllFiniteProducts^.is_prod (factors₁ ++ factors₂ ++ factors₃))
    (λ n, let lim := C_HasAllFiniteProducts^.is_prod (factors₁ ++ [C_HasAllFiniteProducts^.prod factors₂] ++ factors₃)
          in if ω₁ : n^.val < list.length factors₁
              then cast sorry (IsLimit.proj lim { val := n^.val, is_lt := sorry })
              else if ω₂ : n^.val < list.length factors₁ + list.length factors₂
                    then let foo₁ : C_HasAllFiniteProducts^.prod (factors₁ ++ [C_HasAllFiniteProducts^.prod factors₂] ++ factors₃) →→ C_HasAllFiniteProducts^.prod factors₂
                          := cast sorry (IsLimit.proj lim { val := list.length factors₁, is_lt := sorry }) in
                         let foo₂ : C_HasAllFiniteProducts^.prod factors₂ →→ list.get (factors₁ ++ factors₂ ++ factors₃) n
                          := cast sorry (IsLimit.proj (C_HasAllFiniteProducts^.is_prod factors₂) { val := n^.val - list.length factors₁, is_lt := sorry })
                         in foo₂ ∘∘ foo₁
                    else cast sorry (IsLimit.proj lim { val := n^.val - list.length factors₂ + 1, is_lt := sorry }))

/-! #brief definition Explosion of products.
-/
definition HasAllFiniteProducts.explode {C : Cat.{(ℓobj + 1) ℓhom}}
    (C_HasAllFiniteProducts : HasAllFiniteProducts C)
    (factors₁ factors₂ factors₃ : list [[C]])
    : C_HasAllFiniteProducts^.prod (factors₁ ++ factors₂ ++ factors₃)
       →→ C_HasAllFiniteProducts^.prod (factors₁ ++ [C_HasAllFiniteProducts^.prod factors₂] ++ factors₃)
:= IsFiniteProduct.into (C_HasAllFiniteProducts^.is_prod (factors₁ ++ [C_HasAllFiniteProducts^.prod factors₂] ++ factors₃))
    (λ n, let lim := C_HasAllFiniteProducts^.is_prod (factors₁ ++ factors₂ ++ factors₃)
          in if ω₁ : n^.val < list.length factors₁
              then cast sorry (IsLimit.proj lim { val := n^.val, is_lt := sorry })
              else if ω₂ : n^.val < list.length factors₁ + 1
                    then let foo : C_HasAllFiniteProducts^.prod (factors₁ ++ factors₂ ++ factors₃) →→ C_HasAllFiniteProducts^.prod factors₂
                              := IsFiniteProduct.into (C_HasAllFiniteProducts^.is_prod factors₂)
                                  (λ m, cast sorry (IsLimit.proj lim { val := m^.val + list.length factors₁, is_lt := sorry }))
                         in cast sorry foo
                    else cast sorry (IsLimit.proj lim { val := n^.val - 1 + list.length factors₂, is_lt := sorry } ))

/-! #brief Explosion and flattening of products are isomorphisms.
-/
@[reducible] definition HasAllFiniteProducts.flatten_explode_iso {C : Cat.{(ℓobj + 1) ℓhom}}
    (C_HasAllFiniteProducts : HasAllFiniteProducts C)
    (factors₁ factors₂ factors₃ : list [[C]])
    : Iso (HasAllFiniteProducts.flatten C_HasAllFiniteProducts factors₁ factors₂ factors₃)
          (HasAllFiniteProducts.explode C_HasAllFiniteProducts factors₁ factors₂ factors₃)
:= { id₁ := sorry
   , id₂ := sorry
   }

/-! #brief Helper for the pairwise product functor.
-/
@[reducible] definition HasAllFiniteProducts.PairFun₁ {C : Cat.{(ℓobj + 1) ℓhom}}
    {xy₁ xy₂ : [[C ×× C]]}
    (f : (C ×× C)^.hom xy₁ xy₂)
    : ∀ (n : fin 2)
      , FiniteProductDrgm [xy₁^.fst, xy₁^.snd] n →→ FiniteProductDrgm [xy₂^.fst, xy₂^.snd] n
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
            (FiniteProductDrgm factors)
   , is_prod
      := λ factors
         , C_HasAllFiniteLimits^.is_limit (ObjCat.Fin (fin.FinType (list.length factors)))
            (FiniteProductDrgm factors)
   }

end qp
