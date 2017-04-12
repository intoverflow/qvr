/- -----------------------------------------------------------------------
Inductive types.
----------------------------------------------------------------------- -/

import .s3_poly_endofuns

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

end qp