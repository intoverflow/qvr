/- ----------------------------------------------------------------------------
Lambda calculus.
---------------------------------------------------------------------------- -/

namespace Lam

/-! #brief An expression in the lambda calculus.
-/
inductive Expr : ℕ → ℕ → Type
| unit : ∀ {Nf Nb : ℕ}, Expr Nf Nb
| fvar : ∀ {Nf Nb : ℕ} (f : fin Nf), Expr Nf Nb
| bvar : ∀ {Nf Nb : ℕ} (b : fin Nb), Expr Nf Nb
| lam : ∀ {Nf Nb : ℕ} (e : Expr Nf (Nb+1)), Expr Nf Nb
| app : ∀ {Nf Nb : ℕ} (e₁ e₂ : Expr Nf Nb), Expr Nf Nb
| pair : ∀ {Nf Nb : ℕ} (e₁ e₂ : Expr Nf Nb), Expr Nf Nb
| π₁ : ∀ {Nf Nb : ℕ} (e : Expr Nf Nb), Expr Nf Nb
| π₂ : ∀ {Nf Nb : ℕ} (e : Expr Nf Nb), Expr Nf Nb

/-! #brief Lifts a variable.
-/
@[reducible] definition lift_var
    {N : ℕ} (m : fin (N + 1)) (v : fin N)
    : fin (N + 1)
:= if ω : m^.val ≤ v^.val
    then { val := v^.val + 1, is_lt := nat.add_lt_add_right v^.is_lt 1 }
    else { val := v^.val, is_lt := nat.less_than_or_equal.step v^.is_lt }

/-! #brief Shift the bound variables in an expression.
-/
@[reducible] definition shift
    : ∀ (Nf Nb : ℕ) (m : fin (Nb + 1)) (e : Expr Nf Nb)
      , Expr Nf (Nb + 1)
| Nf Nb m Expr.unit := Expr.unit
| Nf Nb m (Expr.fvar s) := Expr.fvar s
| Nf Nb m (Expr.bvar b) := Expr.bvar (lift_var m b)
| Nf Nb m (Expr.lam e) := Expr.lam (shift Nf (Nb + 1) { val := m^.val + 1, is_lt := nat.add_lt_add_right m^.is_lt 1 } e)
| Nf Nb m (Expr.app e₁ e₂) := Expr.app (shift Nf Nb m e₁) (shift Nf Nb m e₂)
| Nf Nb m (Expr.pair e₁ e₂) := Expr.pair (shift Nf Nb m e₁) (shift Nf Nb m e₂)
| Nf Nb m (Expr.π₁ e) := Expr.π₁ (shift Nf Nb m e)
| Nf Nb m (Expr.π₂ e) := Expr.π₂ (shift Nf Nb m e)

/-! #brief Lowers a variable.
-/
@[reducible] definition lower_var
    : ∀ {N M : ℕ} (m : fin N) (v : fin N) (ω : N = M + 1)
      , fin M
| N M m v ω
:= if ω : m^.val ≤ v^.val
    then { val := v^.val - 1, is_lt := sorry }
    else { val := v^.val, is_lt := sorry }

/-! #brief Substitution in the lambda calculus.
-/
@[reducible] definition subst
    : ∀ {Nf Nb : ℕ} (e : Expr Nf Nb)
        {Mb : ℕ} (v : Expr Nf Mb)
        (p : fin Nb)
        (ωNb : Nb = Mb + 1)
      , Expr Nf Mb
| .Nf .Nb (@Expr.unit Nf Nb) Mb v p ωNb := Expr.unit
| .Nf .Nb (@Expr.fvar Nf Nb f) Mb v p ωNb := Expr.fvar f
| .Nf .Nb (@Expr.bvar Nf Nb b) Mb v p ωNb
:= if ωv : b^.val = p^.val
    then v
    else Expr.bvar (lower_var p b ωNb)
| .Nf .Nb (@Expr.lam Nf Nb e) Mb v p ωNb
:= Expr.lam (subst e (shift _ _ { val := 0, is_lt := sorry } v)
                     ({ val := p^.val + 1, is_lt := nat.add_lt_add_right p^.is_lt 1 } )
                     (by rw ωNb))
| .Nf .Nb (@Expr.app Nf Nb e₁ e₂) Mb v p ωNb := Expr.app (subst e₁ v p ωNb) (subst e₂ v p ωNb)
| .Nf .Nb (@Expr.pair Nf Nb e₁ e₂) Mb v p ωNb := Expr.pair (subst e₁ v p ωNb) (subst e₂ v p ωNb)
| .Nf .Nb (@Expr.π₁ Nf Nb e) Mb v p ωNb := Expr.π₁ (subst e v p ωNb)
| .Nf .Nb (@Expr.π₂ Nf Nb e) Mb v p ωNb := Expr.π₂ (subst e v p ωNb)

/-! #brief Guard for beta reduction.
-/
inductive can_beta {Nf Nb : ℕ} : Expr Nf Nb → Prop
| ω : ∀ (e₁ : Expr Nf (Nb + 1)) (e₂ : Expr Nf Nb)
      , can_beta (Expr.app (Expr.lam e₁) e₂)

/-! #brief Applies beta reduction on the head.
-/
@[reducible] definition rule_beta
    : ∀ {Nf Nb : ℕ} (e : Expr Nf Nb)
        (ωe : can_beta e)
      , Expr Nf Nb
| Nf Nb (Expr.app (Expr.lam e₁) e₂) ωe
:= subst e₁ e₂ { val := 0, is_lt := sorry } rfl
| Nf Nb e ωe := e

-- [e1/x1][e2/x2]e = [e2/x2][[e2/x2]e1/x1]e

namespace Examples
open Expr

/-! #brief λ x, λ z, x y
-/
definition ex₁ : Expr 8 2
:= let x : fin 4 := { val := 1, is_lt := sorry } in
   let y : fin 4 := { val := 3, is_lt := sorry }
   in lam (lam (app (bvar x) (bvar y)))

/-! #brief (λ x, λ z, x y)[y ← f] = λ x, λ z, x f
-/
definition ex₁_sub_y
   : let x : fin 3 := { val := 1, is_lt := sorry } in
     let y : fin 2 := { val := 1, is_lt := sorry } in
     let f : fin 8 := { val := 7, is_lt := sorry }
     in subst ex₁ (fvar f) y rfl
         = lam (lam (app (bvar x) (fvar f)))
:= rfl

definition ex₂
    : let x : Expr 8 3 := bvar { val := 2, is_lt := sorry } in
      let y : Expr 8 3 := bvar { val := 1, is_lt := sorry } in
      let z : Expr 8 3 := bvar { val := 0, is_lt := sorry } in
      let F : Expr 8 0 := fvar { val := 7, is_lt := sorry } in
      let y' : Expr 8 2 := bvar { val := 1, is_lt := sorry } in
      let z' : Expr 8 2 := bvar { val := 0, is_lt := sorry } in
      let F' : Expr 8 2 := fvar { val := 7, is_lt := sorry }
      in rule_beta (app (lam (lam (lam (app (app x y) z)))) F) sorry
          = lam (lam (app (app F' y') z'))
:= rfl

definition ex₃
    : let x : Expr 8 3 := bvar { val := 1, is_lt := sorry } in
      let y : Expr 8 3 := bvar { val := 2, is_lt := sorry } in
      let z : Expr 8 3 := bvar { val := 0, is_lt := sorry } in
      let F : Expr 8 0 := fvar { val := 7, is_lt := sorry } in
      let x' : Expr 8 2 := bvar { val := 1, is_lt := sorry } in
      let z' : Expr 8 2 := bvar { val := 0, is_lt := sorry } in
      let F' : Expr 8 2 := fvar { val := 7, is_lt := sorry }
      in rule_beta (app (lam (lam (lam (app (app x y) z)))) F) sorry
          = lam (lam (app (app x' F') z'))
:= rfl

definition ex₄
    : let x : Expr 8 3 := bvar { val := 2, is_lt := sorry } in
      let y : Expr 8 3 := bvar { val := 1, is_lt := sorry } in
      let z : Expr 8 3 := bvar { val := 0, is_lt := sorry } in
      let F : Expr 8 0 := fvar { val := 7, is_lt := sorry } in
      let G : Expr 8 0 := fvar { val := 5, is_lt := sorry } in
      let z' : Expr 8 1 := bvar { val := 0, is_lt := sorry } in
      let F' : Expr 8 1 := fvar { val := 7, is_lt := sorry } in
      let G' : Expr 8 1 := fvar { val := 5, is_lt := sorry }
      in rule_beta (app (rule_beta (app (lam (lam (lam (app (app x y) z)))) F) sorry) G) sorry
          = lam (app (app F' G') z')
:= rfl

end Examples

/-! #brief Guard for left projection.
-/
inductive can_π₁ {Nf Nb : ℕ} : Expr Nf Nb → Prop
| ω : ∀ (e₁ e₂ : Expr Nf Nb)
      , can_π₁ (Expr.π₁ (Expr.pair e₁ e₂))

/-! #brief Applies left projection on the head.
-/
@[reducible] definition rule_π₁
    : ∀ {Nf Nb : ℕ} (e : Expr Nf Nb)
        (ωe : can_π₁ e)
      , Expr Nf Nb
| Nf Nb (Expr.π₁ (Expr.pair e₁ e₂)) ωe := e₁
| Nf Nb e ωe := e

/-! #brief Guard for right projection.
-/
inductive can_π₂ {Nf Nb : ℕ} : Expr Nf Nb → Prop
| ω : ∀ (e₁ e₂ : Expr Nf Nb)
      , can_π₂ (Expr.π₂ (Expr.pair e₁ e₂))

/-! #brief Applies right projection on the head.
-/
@[reducible] definition rule_π₂
    : ∀ {Nf Nb : ℕ} (e : Expr Nf Nb)
        (ωe : can_π₂ e)
      , Expr Nf Nb
| Nf Nb (Expr.π₂ (Expr.pair e₁ e₂)) ωe := e₂
| Nf Nb e ωe := e


namespace STLC
open list

/-! #brief list.nth, but without the option monad.
-/
@[reducible] definition {ℓ} get {A : Type ℓ}
    : ∀ (aa : list A) (idx : fin (length aa))
      , A
| [] (fin.mk idx ω) := begin apply false.rec, cases ω end
| (a :: aa) (fin.mk 0 ω) := a
| (a :: aa) (fin.mk (nat.succ idx) ω) := get aa { val := idx, is_lt := sorry }

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

end Lam
