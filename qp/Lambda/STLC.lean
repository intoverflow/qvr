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

end STLC
end qp
