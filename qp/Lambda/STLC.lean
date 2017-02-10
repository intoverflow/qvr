/- ----------------------------------------------------------------------------
Lambda calculus.
---------------------------------------------------------------------------- -/

import ..util
import .basic

namespace qp
namespace STLC

open Lam
open list

/-! #brief Types in the simplty typed lambda calculus.
-/
inductive Ty : Type
| unit : Ty
| abs : Ty → Ty → Ty
| pair : Ty → Ty → Ty

/-! #brief Typing of expressions.
-/
inductive HasType
    : ∀ (Tf Tb : list Ty)
        (e : Expr (length Tf) (length Tb))
        (τ : Ty)
      , Type
| unit : ∀ {Tf Tb : list Ty}
         , HasType Tf Tb Expr.unit Ty.unit
| fvar : ∀ {Tf Tb : list Ty} (f : fin (length Tf))
         , HasType Tf Tb (Expr.fvar f) (get Tf f)
| bvar : ∀ {Tf Tb : list Ty} (b : fin (length Tb))
         , HasType Tf Tb (Expr.bvar b) (get Tb b)
| lam : ∀ {Tf Tb : list Ty} (τ₁ τ₂ : Ty)
          (e : Expr (length Tf) (length (τ₁ :: Tb)))
          (e_type : HasType Tf (τ₁ :: Tb) e τ₂)
        , HasType Tf Tb (Expr.lam e) (Ty.abs τ₁ τ₂)
| app : ∀ {Tf Tb : list Ty} (τ₁ τ₂ : Ty)
          (e₁ e₂ : Expr (length Tf) (length Tb))
          (e₁_type : HasType Tf Tb e₁ (Ty.abs τ₁ τ₂))
          (e₂_type : HasType Tf Tb e₂ τ₁)
        , HasType Tf Tb (Expr.app e₁ e₂) τ₂
| pair : ∀ {Tf Tb : list Ty} (τ₁ τ₂ : Ty)
           (e₁ e₂ : Expr (length Tf) (length Tb))
           (e₁_type : HasType Tf Tb e₁ τ₁)
           (e₂_type : HasType Tf Tb e₂ τ₂)
         , HasType Tf Tb (Expr.pair e₁ e₂) (Ty.pair τ₁ τ₂)
| π₁ : ∀ {Tf Tb : list Ty} (τ₁ τ₂ : Ty)
         (e : Expr (length Tf) (length Tb))
         (e_type : HasType Tf Tb e (Ty.pair τ₁ τ₂))
       , HasType Tf Tb (Expr.π₁ e) τ₁
| π₂ : ∀ {Tf Tb : list Ty} (τ₁ τ₂ : Ty)
         (e : Expr (length Tf) (length Tb))
         (e_type : HasType Tf Tb e (Ty.pair τ₁ τ₂))
       , HasType Tf Tb (Expr.π₂ e) τ₂

/-! #brief The type theoretic quiver morphism.
-/
@[reducible] definition HasTypeMor (NS : list Notion) (Tf Tb : list Ty) (τ : Ty)
    : RedQvr NS (length Tf) (length Tb) ⇒⇒ FrgtQvr LeanCat
:= { vtx := λ e, HasType Tf Tb e τ
   , arr := λ s, { dom := HasType Tf Tb s^.src τ
                 , codom := HasType Tf Tb s^.dst τ
                 , hom := λ j, sorry
                 }
   , src := λ s, rfl
   , dst := λ s, rfl
   }

/-! #brief The type theoretic functor.
-/
@[reducible] definition HasTypeFun (NS : list Notion) (Tf Tb : list Ty) (τ : Ty)
    : RedCat NS (length Tf) (length Tb) ⇉⇉ LeanCat
:= FreeCat_FrgtQvr_Adj.free_adjoint (HasTypeMor NS Tf Tb τ)

end STLC
end qp
