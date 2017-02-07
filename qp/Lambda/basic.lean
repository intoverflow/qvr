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

/-! #brief Applies beta reduction to the head.
-/
@[reducible] definition rule_app
    : ∀ {Nf : ℕ} (e : Expr Nf 0)
      , Expr Nf 0
| Nf (Expr.app (Expr.lam e₁) e₂) := subst e₁ e₂ { val := 0, is_lt := sorry } rfl
| Nf e := e

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
      in rule_app (app (lam (lam (lam (app (app x y) z)))) F)
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
      in rule_app (app (lam (lam (lam (app (app x y) z)))) F)
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
      in rule_app (app (rule_app (app (lam (lam (lam (app (app x y) z)))) F)) G)
          = lam (app (app F' G') z')
:= rfl


end Examples

end Lam
