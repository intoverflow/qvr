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
@[reducible] definition ProductDrgm {C : Cat.{(ℓobj + 1) ℓhom}} {A : Sort ℓ}
    (factors : A → [[C]])
    : ObjCat A ⇉⇉ C
:= { obj := factors
   , hom := λ m n f, begin cases f, apply C^.id end
   , hom_id := λ m, rfl
   , hom_circ := λ m n p g f, begin cases f, cases g, dsimp, simp, apply rfl end
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



/- ----------------------------------------------------------------------------
Isomorphisms between products.

In particular,
* prod [X₁, ..., Xn] ≅ prod (σ [X₁, ..., Xn]) for any permutation σ
* prod [X₁, ..., Xn, prod [Y₁, ..., Ym], Z₁, ..., Zp]
   ≅ prod [X₁, ..., Xn, Y₁, ..., Ym, Z₁, ..., Zp]
* prod [X₁, ..., Xn, prod [], Z₁, ..., Zp]
   ≅ prod [X₁, ..., Xn, Z₁, ..., Zp]
* prod [X₁] ≅ X₁
---------------------------------------------------------------------------- -/

/-! #brief Permutation of products.
-/
definition HasAllFiniteProducts.perm_limit {C : Cat.{(ℓobj + 1) ℓhom}}
    (C_HasAllFiniteProducts : HasAllFiniteProducts C)
    (factors : list [[C]])
    {perm : fin (list.length factors) → fin (list.length factors)}
    {perm_inv : fin (list.length factors) → fin (list.length factors)}
    (perm_iso : function.isomorphism perm perm_inv)
    : IsProduct (list.get factors)
                (C_HasAllFiniteProducts^.prod (list.perm factors perm_iso))
:= { is_cone
      := { proj
            := λ n, let n' : fin (list.length (list.perm factors perm_iso))
                          := cast (by rw list.perm.length) (perm_inv n) in
                    let h := IsLimit.proj (C_HasAllFiniteProducts^.is_prod (list.perm factors perm_iso)) n'
                    in cast begin
                              assert ω : list.get (list.perm factors perm_iso) n' = list.get factors n,
                              { exact sorry },
                              dsimp, rw ω
                            end
                        h
         , triangle
            := λ n₁ n₂ f, begin cases f, simp end
         }
   , is_final
      := { final := sorry
         , uniq := sorry
         }
   }

/-! #brief The un-permuting hom.
-/
definition HasAllFiniteProducts.unperm {C : Cat.{(ℓobj + 1) ℓhom}}
    (C_HasAllFiniteProducts : HasAllFiniteProducts C)
    (factors : list [[C]])
    {perm : fin (list.length factors) → fin (list.length factors)}
    {perm_inv : fin (list.length factors) → fin (list.length factors)}
    (perm_iso : function.isomorphism perm perm_inv)
    : C_HasAllFiniteProducts^.prod (list.perm factors perm_iso)
       →→ C_HasAllFiniteProducts^.prod factors
:= IsLimit.mediate (C_HasAllFiniteProducts^.is_prod factors)
    (HasAllFiniteProducts.perm_limit C_HasAllFiniteProducts factors perm_iso)^.is_cone

/-! #brief The permuting hom.
-/
definition HasAllFiniteProducts.perm {C : Cat.{(ℓobj + 1) ℓhom}}
    (C_HasAllFiniteProducts : HasAllFiniteProducts C)
    (factors : list [[C]])
    {perm : fin (list.length factors) → fin (list.length factors)}
    {perm_inv : fin (list.length factors) → fin (list.length factors)}
    (perm_iso : function.isomorphism perm perm_inv)
    : C_HasAllFiniteProducts^.prod factors
       →→ C_HasAllFiniteProducts^.prod (list.perm factors perm_iso)
:= IsLimit.mediate (HasAllFiniteProducts.perm_limit C_HasAllFiniteProducts factors perm_iso)
    (C_HasAllFiniteProducts^.is_prod factors)^.is_cone

/-! #brief Permuting and unpermuting of products are isomorphisms.

prod [X₁, ..., Xn] ≅ prod (σ [X₁, ..., Xn]) for any permutation σ of [1,...,n].
-/
@[reducible] definition HasAllFiniteProducts.unpermute_permute_iso {C : Cat.{(ℓobj + 1) ℓhom}}
    (C_HasAllFiniteProducts : HasAllFiniteProducts C)
    (factors : list [[C]])
    {perm : fin (list.length factors) → fin (list.length factors)}
    {perm_inv : fin (list.length factors) → fin (list.length factors)}
    (perm_iso : function.isomorphism perm perm_inv)
    : Iso (HasAllFiniteProducts.unperm C_HasAllFiniteProducts factors perm_iso)
          (HasAllFiniteProducts.perm C_HasAllFiniteProducts factors perm_iso)
:= IsLimit.iso (HasAllFiniteProducts.perm_limit C_HasAllFiniteProducts factors perm_iso)
               (C_HasAllFiniteProducts^.is_prod factors)

/-! #brief Flattening of products of products.
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

prod [X₁, ..., Xn, prod [Y₁, ..., Ym], Z₁, ..., Zp]
 ≅ prod [X₁, ..., Xn, Y₁, ..., Ym, Z₁, ..., Zp]
-/
@[reducible] definition HasAllFiniteProducts.flatten_explode_iso {C : Cat.{(ℓobj + 1) ℓhom}}
    (C_HasAllFiniteProducts : HasAllFiniteProducts C)
    (factors₁ factors₂ factors₃ : list [[C]])
    : Iso (HasAllFiniteProducts.flatten C_HasAllFiniteProducts factors₁ factors₂ factors₃)
          (HasAllFiniteProducts.explode C_HasAllFiniteProducts factors₁ factors₂ factors₃)
:= IsLimit.iso (HasAllFiniteProducts.flat_limit C_HasAllFiniteProducts factors₁ factors₂ factors₃)
               (C_HasAllFiniteProducts^.is_prod (factors₁ ++ factors₂ ++ factors₃))

/-! #brief Flattening of products of empty products.
-/
definition HasAllFiniteProducts.unit_limit {C : Cat.{(ℓobj + 1) ℓhom}}
    (C_HasAllFiniteProducts : HasAllFiniteProducts C)
    (factors₁ factors₃ : list [[C]])
    : IsProduct (list.get (factors₁ ++ factors₃))
                (C_HasAllFiniteProducts^.prod (factors₁ ++ [C_HasAllFiniteProducts^.prod [] ] ++ factors₃))
:= { is_cone
      := { proj
            := λ n
               , let lim := C_HasAllFiniteProducts^.is_prod (factors₁ ++ [C_HasAllFiniteProducts^.prod [] ] ++ factors₃)
                 in if ω₁ : n^.val < list.length factors₁
                     then cast sorry (IsLimit.proj lim { val := n^.val, is_lt := sorry })
                     else cast sorry (IsLimit.proj lim { val := n^.val - list.length factors₁, is_lt := sorry })
         , triangle
            := λ n₁ n₂ f, begin cases f, simp end
         }
   , is_final
      := { final := sorry
         , uniq := sorry
         }
   }

/-! #brief The unit-dropping hom.
-/
definition HasAllFiniteProducts.unit_drop {C : Cat.{(ℓobj + 1) ℓhom}}
    (C_HasAllFiniteProducts : HasAllFiniteProducts C)
    (factors₁ factors₃ : list [[C]])
    : C_HasAllFiniteProducts^.prod (factors₁ ++ [C_HasAllFiniteProducts^.prod [] ] ++ factors₃)
       →→ C_HasAllFiniteProducts^.prod (factors₁ ++ factors₃)
:= IsLimit.mediate (C_HasAllFiniteProducts^.is_prod (factors₁ ++ factors₃))
    (HasAllFiniteProducts.unit_limit C_HasAllFiniteProducts factors₁ factors₃)^.is_cone

/-! #brief The unit-inserting hom.
-/
definition HasAllFiniteProducts.unit_insert {C : Cat.{(ℓobj + 1) ℓhom}}
    (C_HasAllFiniteProducts : HasAllFiniteProducts C)
    (factors₁ factors₃ : list [[C]])
    : C_HasAllFiniteProducts^.prod (factors₁ ++ factors₃)
       →→ C_HasAllFiniteProducts^.prod (factors₁ ++ [C_HasAllFiniteProducts^.prod [] ] ++ factors₃)
:= IsLimit.mediate (HasAllFiniteProducts.unit_limit C_HasAllFiniteProducts factors₁ factors₃)
    (C_HasAllFiniteProducts^.is_prod (factors₁ ++ factors₃))^.is_cone

/-! #brief Dropping and insertion of units of products are isomorphisms.

prod [X₁, ..., Xn, prod [], Z₁, ..., Zp]
 ≅ prod [X₁, ..., Xn, Z₁, ..., Zp]
-/
@[reducible] definition HasAllFiniteProducts.unit_drop_insert_iso {C : Cat.{(ℓobj + 1) ℓhom}}
    (C_HasAllFiniteProducts : HasAllFiniteProducts C)
    (factors₁ factors₃ : list [[C]])
    : Iso (HasAllFiniteProducts.unit_drop C_HasAllFiniteProducts factors₁ factors₃)
          (HasAllFiniteProducts.unit_insert C_HasAllFiniteProducts factors₁ factors₃)
:= IsLimit.iso (HasAllFiniteProducts.unit_limit C_HasAllFiniteProducts factors₁ factors₃)
               (C_HasAllFiniteProducts^.is_prod (factors₁ ++ factors₃))

/-! #brief Singleton products.
-/
definition HasAllFiniteProducts.singleton_limit {C : Cat.{(ℓobj + 1) ℓhom}}
    (C_HasAllFiniteProducts : HasAllFiniteProducts C)
    (x : [[C]])
    : IsProduct (list.get [x]) x
:= { is_cone
      := { proj := λ n, match n with
                          | (fin.mk 0 ωn) := ⟨⟨x⟩⟩
                          | (fin.mk (nat.succ n) ωn) := false.cases_on _ begin cases ωn, cases a end
                        end
         , triangle
            := λ n₁ n₂ f, begin cases f, simp end
         }
   , is_final
      := { final := sorry
         , uniq := sorry
         }
   }

/-! #brief The singleton unboxing hom.
-/
definition HasAllFiniteProducts.singleton_unbox {C : Cat.{(ℓobj + 1) ℓhom}}
    (C_HasAllFiniteProducts : HasAllFiniteProducts C)
    (x : [[C]])
    : C_HasAllFiniteProducts^.prod [x] →→ x
:= IsLimit.mediate (HasAllFiniteProducts.singleton_limit C_HasAllFiniteProducts x)
    (C_HasAllFiniteProducts^.is_prod [x])^.is_cone

/-! #brief The singleton boxing hom.
-/
definition HasAllFiniteProducts.singleton_box {C : Cat.{(ℓobj + 1) ℓhom}}
    (C_HasAllFiniteProducts : HasAllFiniteProducts C)
    (x : [[C]])
    : x →→ C_HasAllFiniteProducts^.prod [x]
:= IsLimit.mediate (C_HasAllFiniteProducts^.is_prod [x])
    (HasAllFiniteProducts.singleton_limit C_HasAllFiniteProducts x)^.is_cone

/-! #brief Unboxing and boxing are isomorphisms.

prod [X₁] ≅ X₁
-/
@[reducible] definition HasAllFiniteProducts.singleton_unbox_box_iso {C : Cat.{(ℓobj + 1) ℓhom}}
    (C_HasAllFiniteProducts : HasAllFiniteProducts C)
    (x : [[C]])
    : Iso (HasAllFiniteProducts.singleton_unbox C_HasAllFiniteProducts x)
          (HasAllFiniteProducts.singleton_box C_HasAllFiniteProducts x)
:= IsLimit.iso (C_HasAllFiniteProducts^.is_prod [x])
               (HasAllFiniteProducts.singleton_limit C_HasAllFiniteProducts x)



/- ----------------------------------------------------------------------------
The pair functor.
---------------------------------------------------------------------------- -/

/-! #brief Helper for the pairwise product functor.
-/
@[reducible] definition HasAllFiniteProducts.PairFun_helper {C : Cat.{(ℓobj + 1) ℓhom}}
    {xy₁ xy₂ : [[C ×× C]]}
    (f : (C ×× C)^.hom xy₁ xy₂)
    : ∀ (n : fin 2)
      , ProductDrgm (list.get [xy₁^.fst, xy₁^.snd]) n
         →→ ProductDrgm (list.get [xy₂^.fst, xy₂^.snd]) n
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
            { proj := λ n, HasAllFiniteProducts.PairFun_helper f n
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

/-! #brief The pairwise product functor.
-/
@[reducible] definition HasAllFiniteProducts.PairFun.BraidTrans {C : Cat.{(ℓobj + 1) ℓhom}}
    (C_HasAllFiniteProducts : HasAllFiniteProducts C)
    : HasAllFiniteProducts.PairFun C_HasAllFiniteProducts
       ↣↣ HasAllFiniteProducts.PairFun C_HasAllFiniteProducts □□ ProdCat.flip
:= { component := λ c, cast sorry (HasAllFiniteProducts.perm C_HasAllFiniteProducts [c^.fst, c^.snd] fin.minus_perm.iso)
   , transport := λ x y f, sorry
   }

/- ----------------------------------------------------------------------------
Cartesian monoidal categories.
---------------------------------------------------------------------------- -/

/-! #brief Every category with all finite products is a cartesian monoidal category.
-/
@[reducible] definition HasAllFiniteProducts.Monoidal {C : Cat.{(ℓobj + 1) ℓhom}}
    (C_HasAllFiniteProducts : HasAllFiniteProducts C)
    : IsMonoidal C
       (HasAllFiniteProducts.PairFun C_HasAllFiniteProducts)
       (C_HasAllFiniteProducts^.prod [])
:= { assoc_left
      := { component := λ xyz, HasAllFiniteProducts.explode C_HasAllFiniteProducts [] [xyz^.fst, xyz^.snd^.fst] [xyz^.snd^.snd]
                                ∘∘ HasAllFiniteProducts.flatten C_HasAllFiniteProducts [xyz^.fst] [xyz^.snd^.fst, xyz^.snd^.snd] []
         , transport := λ xyz₁ xyz₂ f, sorry
         }
   , assoc_right
      := { component := λ xyz, HasAllFiniteProducts.explode C_HasAllFiniteProducts [xyz^.fst] [xyz^.snd^.fst, xyz^.snd^.snd] []
                                ∘∘ HasAllFiniteProducts.flatten C_HasAllFiniteProducts [] [xyz^.fst, xyz^.snd^.fst] [xyz^.snd^.snd]
         , transport := λ xyz₁ xyz₂ f, sorry
         }
   , assoc_iso :=
      { id₁ := NatTrans.eq
                (λ x, sorry)
      , id₂ := NatTrans.eq
                (λ x, sorry)
      }
   , left_unitor
      := { component := λ x, HasAllFiniteProducts.singleton_unbox C_HasAllFiniteProducts x
                              ∘∘ HasAllFiniteProducts.unit_drop C_HasAllFiniteProducts [] [x]
         , transport := begin exact sorry end
         }
   , left_unitor_inv
      := { component := λ x, HasAllFiniteProducts.unit_insert C_HasAllFiniteProducts [] [x]
                              ∘∘ HasAllFiniteProducts.singleton_box C_HasAllFiniteProducts x
         , transport := begin exact sorry end
         }
   , left_unitor_iso := begin exact sorry end
   , right_unitor
      := { component := λ x, HasAllFiniteProducts.singleton_unbox C_HasAllFiniteProducts x
                              ∘∘ HasAllFiniteProducts.unit_drop C_HasAllFiniteProducts [x] []
         , transport := begin exact sorry end
         }
   , right_unitor_inv
      := { component := λ x, HasAllFiniteProducts.unit_insert C_HasAllFiniteProducts [x] []
                              ∘∘ HasAllFiniteProducts.singleton_box C_HasAllFiniteProducts x
         , transport := begin exact sorry end
         }
   , right_unitor_iso := begin exact sorry end
   , triangle := begin exact sorry end
   , pentagon := begin exact sorry end
   }

/-! #brief Cartesian monoidal categories are symmetric.
-/
theorem HasAllFiniteProducts.Symmetric {C : Cat.{(ℓobj + 1) ℓhom}}
    (C_HasAllFiniteProducts : HasAllFiniteProducts C)
    : IsSymmetric C
        (HasAllFiniteProducts.Monoidal C_HasAllFiniteProducts)
        (HasAllFiniteProducts.PairFun.BraidTrans C_HasAllFiniteProducts)
:= { unbraid_braid_iso
      := { id₁ := begin apply NatTrans.eq, intro c, cases c with c₁ c₂, dsimp, exact sorry end
         , id₂ := sorry
         }
   , hex_left := sorry
   , hex_right := sorry
   }

end qp
