/- -----------------------------------------------------------------------
Inductive types.
----------------------------------------------------------------------- -/

import .s5_wtypes

namespace qp

open stdaux

universe variables ℓobj ℓhom



/- -----------------------------------------------------------------------
Inductive signatures.
----------------------------------------------------------------------- -/

/-! #brief Signature for a constructor.
-/
definition ConSig (C : Cat.{ℓobj ℓhom})
    : Type ℓobj
:= ℕ × list C^.obj

/-! #brief The arguments of a constructor signature.
-/
definition ConSig.args {C : Cat.{ℓobj ℓhom}}
    [C_HasAllFinProducts : HasAllFinProducts C]
    (σ : ConSig C)
    : C^.obj
:= finproduct C σ^.snd

/-! #brief The domain of a constructor signature.
-/
definition ConSig.dom {C : Cat.{ℓobj ℓhom}}
    [C_HasAllFinProducts : HasAllFinProducts C]
    [C_HasAllFinCoProducts : HasAllFinCoProducts C]
    (σ : ConSig C)
    : C^.obj
:= fincoproduct C (list.repeat σ^.args σ^.fst)

/-! #brief The codomain of a constructor signature.
-/
definition ConSig.codom {C : Cat.{ℓobj ℓhom}}
    [C_HasAllFinProducts : HasAllFinProducts C]
    [C_HasAllFinCoProducts : HasAllFinCoProducts C]
    (σ : ConSig C)
    : C^.obj
:= σ^.args

/-! #brief The domain/codomain pair of a constructor signature.
-/
definition ConSig.between {C : Cat.{ℓobj ℓhom}}
    [C_HasAllFinProducts : HasAllFinProducts C]
    [C_HasAllFinCoProducts : HasAllFinCoProducts C]
    (σ : ConSig C)
    : prod C^.obj C^.obj
:= (σ^.dom, σ^.codom)

/-! #brief The hom induced by a constructor signature.
-/
definition ConSig.induce {C : Cat.{ℓobj ℓhom}}
    [C_HasAllFinProducts : HasAllFinProducts C]
    [C_HasAllFinCoProducts : HasAllFinCoProducts C]
    (σ : ConSig C)
    : C^.hom σ^.dom σ^.codom
:= fincoproduct.univ C (list.repeat σ^.args σ^.fst)
    (HomsIn.repeat (C^.id σ^.args) σ^.fst)

/-! #brief An inductive signature.
-/
definition IndSig (C : Cat.{ℓobj ℓhom})
    : Type ℓobj
:= list (ConSig C)

/-! #brief Converting an inductive signature to a list of homs.
-/
definition IndSig.between {C : Cat.{ℓobj ℓhom}}
    [C_HasAllFinProducts : HasAllFinProducts C]
    [C_HasAllFinCoProducts : HasAllFinCoProducts C]
    (σσ : IndSig C)
    : list (prod C^.obj C^.obj)
:= list.map ConSig.between σσ

/-! #brief Converting an inductive signature to a list of homs.
-/
definition IndSig.HomsList {C : Cat.{ℓobj ℓhom}}
    [C_HasAllFinProducts : HasAllFinProducts C]
    [C_HasAllFinCoProducts : HasAllFinCoProducts C]
    : ∀ (σσ : IndSig C)
      , HomsList C (IndSig.between σσ)
| [] := HomsList.nil
| (σ :: σσ) := HomsList.cons σ^.induce (IndSig.HomsList σσ)

/-! #brief The hom induced by an inductive signature.
-/
definition IndSig.induce {C : Cat.{ℓobj ℓhom}}
    [C_HasAllFinProducts : HasAllFinProducts C]
    [C_HasAllFinCoProducts : HasAllFinCoProducts C]
    (σσ : IndSig C)
    : C^.hom (fincoproduct C (list.map ConSig.dom σσ))
             (fincoproduct C (list.map ConSig.codom σσ))
:= cast_hom begin
              apply fincoproduct.eq,
              apply list.map_map
            end
   ∘∘ fincoproduct.hom (IndSig.HomsList σσ)
   ∘∘ cast_hom begin
                 apply fincoproduct.eq,
                 apply eq.symm,
                 apply list.map_map
               end



/- -----------------------------------------------------------------------
Categories with inductive types.
----------------------------------------------------------------------- -/

/-! #brief A category with an inductive type.
-/
@[class] definition HasIndType (C : Cat.{ℓobj ℓhom})
    [C_HasFinal : HasFinal C]
    [C_HasDepProd : HasDepProd C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasAllFinProducts : HasAllFinProducts C]
    [C_HasAllFinCoProducts : HasAllFinCoProducts C]
    (σ : IndSig C)
:= HasWType C σ^.induce

/-! #brief An inductive type.
-/
definition indType (C : Cat.{ℓobj ℓhom})
    [C_HasFinal : HasFinal C]
    [C_HasDepProd : HasDepProd C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasAllFinProducts : HasAllFinProducts C]
    [C_HasAllFinCoProducts : HasAllFinCoProducts C]
    (σ : IndSig C)
    [σ_HasIndType : HasIndType C σ]
    : C^.obj
:= @wtype.carr C
      C_HasAllFinProducts
      C_HasFinal
      C_HasDepProd
      C_HasAllPullbacks
      _ _ σ^.induce
      σ_HasIndType

/-! #brief Generic constructor for an inductive type.
-/
definition indType.mk' (C : Cat.{ℓobj ℓhom})
    [C_HasFinal : HasFinal C]
    [C_HasDepProd : HasDepProd C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasAllFinProducts : HasAllFinProducts C]
    [C_HasAllFinCoProducts : HasAllFinCoProducts C]
    (σ : IndSig C)
    [σ_HasIndType : HasIndType C σ]
    : C^.hom ((PolyEndoFun σ^.induce)^.obj (indType C σ))
             (indType C σ)
:= @wtype.hom C
      C_HasAllFinProducts
      C_HasFinal
      C_HasDepProd
      C_HasAllPullbacks
      _ _ σ^.induce
      σ_HasIndType

/-! #brief Generic eliminator for an inductive type.
-/
definition indType.elim' (C : Cat.{ℓobj ℓhom})
    [C_HasFinal : HasFinal C]
    [C_HasDepProd : HasDepProd C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasAllFinProducts : HasAllFinProducts C]
    [C_HasAllFinCoProducts : HasAllFinCoProducts C]
    (σ : IndSig C)
    [σ_HasIndType : HasIndType C σ]
    : C^.hom (indType C σ)
             ((PolyEndoFun σ^.induce)^.obj (indType C σ))
:= @wtype.elim C
      C_HasAllFinProducts
      C_HasFinal
      C_HasDepProd
      C_HasAllPullbacks
      _ _ σ^.induce
      σ_HasIndType

/-! #brief Construction/elimination is an iso.
-/
definition indType.iso' (C : Cat.{ℓobj ℓhom})
    [C_HasFinal : HasFinal C]
    [C_HasDepProd : HasDepProd C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasAllFinProducts : HasAllFinProducts C]
    [C_HasAllFinCoProducts : HasAllFinCoProducts C]
    (σ : IndSig C)
    [σ_HasIndType : HasIndType C σ]
    : Iso (indType.mk' C σ) (indType.elim' C σ)
:= @wtype.iso C
      C_HasAllFinProducts
      C_HasFinal
      C_HasDepProd
      C_HasAllPullbacks
      _ _ σ^.induce
      σ_HasIndType

/-! #brief Arguments for the n-th constructor.
-/
definition indType.arg (C : Cat.{ℓobj ℓhom})
    [C_HasFinal : HasFinal C]
    [C_HasDepProd : HasDepProd C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasAllFinProducts : HasAllFinProducts C]
    [C_HasAllFinCoProducts : HasAllFinCoProducts C]
    (σσ : IndSig C)
    [σ_HasIndType : HasIndType C σσ]
    (σ : ConSig C)
    : C^.obj
:= finproduct C [σ^.args, finproduct C (list.repeat (indType C σσ) σ^.fst)]

/-! #brief Decomposition of an inductive type in terms of its constructors.
-/
definition indType.decomp (C : Cat.{ℓobj ℓhom})
    [C_HasFinal : HasFinal C]
    [C_HasDepProd : HasDepProd C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasAllFinProducts : HasAllFinProducts C]
    [C_HasAllFinCoProducts : HasAllFinCoProducts C]
    (σ : IndSig C)
    [σ_HasIndType : HasIndType C σ]
    : C^.obj
:= fincoproduct C (list.map (indType.arg C σ) σ)

-- /-! #brief Algebra structure on the decomposition of an inductive type.
-- -/
-- definition indType.alg (C : Cat.{ℓobj ℓhom})
--     [C_HasFinal : HasFinal C]
--     [C_HasDepProd : HasDepProd C]
--     [C_HasAllPullbacks : HasAllPullbacks C]
--     [C_HasAllFinProducts : HasAllFinProducts C]
--     [C_HasAllFinCoProducts : HasAllFinCoProducts C]
--     (σ : IndSig C)
--     [σ_HasIndType : HasIndType C σ]
--     : EndoAlg (PolyEndoFun σ^.induce)
-- := { carr := indType.decomp C σ
--    , hom := sorry
--    }

-- /-! #brief Hom from the n-th constructor arguments to the induced codomain.
-- -/
-- definition indType.args.over (C : Cat.{ℓobj ℓhom})
--     [C_HasFinal : HasFinal C]
--     [C_HasDepProd : HasDepProd C]
--     [C_HasAllPullbacks : HasAllPullbacks C]
--     [C_HasAllFinProducts : HasAllFinProducts C]
--     [C_HasAllFinCoProducts : HasAllFinCoProducts C]
--     (σ : IndSig C)
--     [σ_HasIndType : HasIndType C σ]
--     : ∀ (n : fin (list.length σ))
--       , C^.hom (indType.args C σ n)
--                (fincoproduct C (list.map ConSig.codom σ))
-- | (fin.mk n ωn)
-- := fincoproduct.ι C (list.map ConSig.codom σ)
--     { val := n, is_lt := cast begin rw list.length_map end ωn }
--     ∘∘ cast_hom begin rw -list.get_map, { trivial }, { rw list.length_map } end
--     ∘∘ finproduct.π C _ (@fin_of 1 0)

-- /-! #brief Generic constructor for an inductive type.
-- -/
-- definition indType.mk (C : Cat.{ℓobj ℓhom})
--     [C_HasFinal : HasFinal C]
--     [C_HasDepProd : HasDepProd C]
--     [C_HasAllPullbacks : HasAllPullbacks C]
--     [C_HasAllFinProducts : HasAllFinProducts C]
--     [C_HasAllFinCoProducts : HasAllFinCoProducts C]
--     (σ : IndSig C)
--     [σ_HasIndType : HasIndType C σ]
--     (n : fin (list.length σ))
--     : C^.hom (indType.args C σ n)
--              (indType C σ)
-- := indType.mk' C σ
--     ∘∘ PolyEndoFun.into σ^.induce (indType.args.over C σ n)
--         (begin end)

end qp
