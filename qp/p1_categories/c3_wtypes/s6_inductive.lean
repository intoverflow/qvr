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
structure ConSig (C : Cat.{ℓobj ℓhom})
    : Type ℓobj
:= (rec_arity : ℕ)
   (args : list C^.obj)

/-! #brief The non-recursive arguments of a constructor signature.
-/
definition ConSig.arg {C : Cat.{ℓobj ℓhom}}
    [C_HasAllFinProducts : HasAllFinProducts C]
    (conσ : ConSig C)
    : C^.obj
:= finproduct C conσ^.args

/-! #brief An inductive signature.
-/
definition IndSig (C : Cat.{ℓobj ℓhom})
    : Type ℓobj
:= list (ConSig C)



/- -----------------------------------------------------------------------
Representing hom for a constructor.
----------------------------------------------------------------------- -/

/-! #brief The domain of the representing hom for a constructor.
-/
definition ConSig.rep.dom {C : Cat.{ℓobj ℓhom}}
    [C_HasAllFinProducts : HasAllFinProducts C]
    [C_HasAllFinCoProducts : HasAllFinCoProducts C]
    (conσ : ConSig C)
    : C^.obj
:= fincoproduct C (list.repeat conσ^.arg conσ^.rec_arity)

/-! #brief The codomain of the representing hom for a constructor.
-/
definition ConSig.rep.codom {C : Cat.{ℓobj ℓhom}}
    [C_HasAllFinProducts : HasAllFinProducts C]
    [C_HasAllFinCoProducts : HasAllFinCoProducts C]
    (conσ : ConSig C)
    : C^.obj
:= conσ^.arg

/-! #brief The domain/codomain pair of the representing hom for a constructor.
-/
definition ConSig.rep.dom_codom {C : Cat.{ℓobj ℓhom}}
    [C_HasAllFinProducts : HasAllFinProducts C]
    [C_HasAllFinCoProducts : HasAllFinCoProducts C]
    (conσ : ConSig C)
    : prod C^.obj C^.obj
:= (conσ^.rep.dom, conσ^.rep.codom)

/-! #brief The representing hom for a constructor.
-/
definition ConSig.rep {C : Cat.{ℓobj ℓhom}}
    [C_HasAllFinProducts : HasAllFinProducts C]
    [C_HasAllFinCoProducts : HasAllFinCoProducts C]
    (conσ : ConSig C)
    : C^.hom conσ^.rep.dom conσ^.rep.codom
:= fincoproduct.univ C (list.repeat conσ^.arg conσ^.rec_arity)
    (HomsIn.repeat (C^.id conσ^.arg) conσ^.rec_arity)



/- -----------------------------------------------------------------------
Polynomial endo-functors induced by inductive signatures.
----------------------------------------------------------------------- -/

/-! #brief The polynomial endo-functor associated with a constructor.
-/
definition ConSig.PolyEndoFun {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasDepProd : HasAllDepProd C]
    [C_HasAllFinProducts : HasAllFinProducts C]
    [C_HasAllFinCoProducts : HasAllFinCoProducts C]
    (conσ : ConSig C)
    : PolyEndoFun C
:= PolyEndoFun.of_hom conσ^.rep

/-! #brief The polynomial endo-functor associated with an inductive signature.
-/
definition IndSig.PolyEndoFun {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasDepProd : HasAllDepProd C]
    [C_HasAllFinProducts : HasAllFinProducts C]
    [C_HasAllFinCoProducts : HasAllFinCoProducts C]
    (indσ : IndSig C)
    : PolyEndoFun C
:= PolyEndoFun.sum (list.map ConSig.PolyEndoFun indσ)



/- -----------------------------------------------------------------------
Categories with inductive types.
----------------------------------------------------------------------- -/

/-! #brief A category with an inductive type.
-/
@[class] definition HasIndType (C : Cat.{ℓobj ℓhom})
    [C_HasFinal : HasFinal C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasDepProd : HasAllDepProd C]
    [C_HasAllFinProducts : HasAllFinProducts C]
    [C_HasAllFinCoProducts : HasAllFinCoProducts C]
    (indσ : IndSig C)
:= HasWType C indσ^.PolyEndoFun

/-! #brief An inductive type.
-/
definition IndSig.prim {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasDepProd : HasAllDepProd C]
    [C_HasAllFinProducts : HasAllFinProducts C]
    [C_HasAllFinCoProducts : HasAllFinCoProducts C]
    (indσ : IndSig C)
    [σ_HasIndType : HasIndType C indσ]
    : C^.obj
:= @wtype.carr C
      C_HasAllFinProducts
      C_HasFinal
      C_HasAllPullbacks
      C_HasDepProd
      indσ^.PolyEndoFun
      σ_HasIndType

/-! #brief Primitive folding an inductive type.
-/
definition IndSig.prim_fold {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasDepProd : HasAllDepProd C]
    [C_HasAllFinProducts : HasAllFinProducts C]
    [C_HasAllFinCoProducts : HasAllFinCoProducts C]
    (indσ : IndSig C)
    [σ_HasIndType : HasIndType C indσ]
    : C^.hom (indσ^.PolyEndoFun^.endo^.obj indσ^.prim)
             indσ^.prim
:= @wtype.fold C
      C_HasAllFinProducts
      C_HasFinal
      C_HasAllPullbacks
      C_HasDepProd
      indσ^.PolyEndoFun
      σ_HasIndType

/-! #brief Primitive unfolding an inductive type.
-/
definition IndSig.prim_unfold {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasDepProd : HasAllDepProd C]
    [C_HasAllFinProducts : HasAllFinProducts C]
    [C_HasAllFinCoProducts : HasAllFinCoProducts C]
    (indσ : IndSig C)
    [σ_HasIndType : HasIndType C indσ]
    : C^.hom indσ^.prim
             (indσ^.PolyEndoFun^.endo^.obj indσ^.prim)
:= @wtype.unfold C
      C_HasAllFinProducts
      C_HasFinal
      C_HasAllPullbacks
      C_HasDepProd
      indσ^.PolyEndoFun
      σ_HasIndType

/-! #brief Primitive fold/unfold is an iso.
-/
definition IndSig.prim_iso (C : Cat.{ℓobj ℓhom})
    [C_HasFinal : HasFinal C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasDepProd : HasAllDepProd C]
    [C_HasAllFinProducts : HasAllFinProducts C]
    [C_HasAllFinCoProducts : HasAllFinCoProducts C]
    (indσ : IndSig C)
    [σ_HasIndType : HasIndType C indσ]
    : Iso indσ^.prim_fold indσ^.prim_unfold
:= @wtype.iso C
      C_HasAllFinProducts
      C_HasFinal
      C_HasAllPullbacks
      C_HasDepProd
      indσ^.PolyEndoFun
      σ_HasIndType

/-! #brief Arguments for the n-th constructor.
-/
definition IndSig.con_arg {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasDepProd : HasAllDepProd C]
    [C_HasAllFinProducts : HasAllFinProducts C]
    [C_HasAllFinCoProducts : HasAllFinCoProducts C]
    (indσ : IndSig C)
    [indσ_HasIndType : HasIndType C indσ]
    (σ : ConSig C)
    : C^.obj
:= finproduct C ((list.repeat indσ^.prim σ^.rec_arity) ++ σ^.args)

/-! #brief Decomposition of an inductive type in terms of its constructors.
-/
definition IndSig.type {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    [C_HasDepProd : HasAllDepProd C]
    [C_HasAllFinProducts : HasAllFinProducts C]
    [C_HasAllFinCoProducts : HasAllFinCoProducts C]
    (indσ : IndSig C)
    [indσ_HasIndType : HasIndType C indσ]
    : C^.obj
:= fincoproduct C (list.map indσ^.con_arg indσ)

end qp
