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

/-! #brief Shift the bound variables.
-/
@[reducible] definition shift
    : ∀ (Nf Nb : ℕ) (m : fin (Nb + 1)) (e : Expr Nf Nb)
      , Expr Nf (Nb + 1)
| Nf Nb m Expr.unit := Expr.unit
| Nf Nb m (Expr.fvar s) := Expr.fvar s
| Nf Nb m (Expr.bvar b)
:= if b^.val < m^.val
    then Expr.bvar { val := b^.val, is_lt := nat.less_than_or_equal.step b^.is_lt }
    else Expr.bvar { val := b^.val + 1, is_lt := nat.add_lt_add_right b^.is_lt 1 }
| Nf Nb m (Expr.lam e) := Expr.lam (shift Nf (Nb + 1) { val := m^.val + 1, is_lt := nat.add_lt_add_right m^.is_lt 1 } e)
| Nf Nb m (Expr.app e₁ e₂) := Expr.app (shift Nf Nb m e₁) (shift Nf Nb m e₂)
| Nf Nb m (Expr.pair e₁ e₂) := Expr.pair (shift Nf Nb m e₁) (shift Nf Nb m e₂)
| Nf Nb m (Expr.π₁ e) := Expr.π₁ (shift Nf Nb m e)
| Nf Nb m (Expr.π₂ e) := Expr.π₂ (shift Nf Nb m e)

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
    else if ωv' : b^.val < p^.val
          then Expr.bvar { val := b^.val, is_lt := sorry }
          else Expr.bvar { val := b^.val - 1, is_lt := sorry }
| .Nf .Nb (@Expr.lam Nf Nb e) Mb v p ωNb
:= Expr.lam (subst e (shift _ _ { val := 0, is_lt := sorry } v)
                     ({ val := p^.val + 1, is_lt := nat.add_lt_add_right p^.is_lt 1 } )
                     (by rw ωNb))
| .Nf .Nb (@Expr.app Nf Nb e₁ e₂) Mb v p ωNb := Expr.app (subst e₁ v p ωNb) (subst e₂ v p ωNb)
| .Nf .Nb (@Expr.pair Nf Nb e₁ e₂) Mb v p ωNb := Expr.pair (subst e₁ v p ωNb) (subst e₂ v p ωNb)
| .Nf .Nb (@Expr.π₁ Nf Nb e) Mb v p ωNb := Expr.π₁ (subst e v p ωNb)
| .Nf .Nb (@Expr.π₂ Nf Nb e) Mb v p ωNb := Expr.π₂ (subst e v p ωNb)

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

end Examples

/-
| Nf Nb m v Expr.unit := Expr.unit
| Nf Nb m v (Expr.fvar s) := Expr.fvar s
| Nf Nb m v (Expr.bvar n)
:= if ωv : n^.val = m^.val
    then v
    else if ωv' : n^.val < m^.val
          then Expr.bvar { val := n^.val, is_lt := sorry }
          else Expr.bvar { val := n^.val - 1, is_lt := sorry }
| Nf Nb m v (Expr.lam e)
:= let m' : fin (Nb + 2) := { val := m^.val, is_lt := sorry } -- nat.less_than_or_equal.step m^.is_lt }
   in Expr.lam (subst m' (shift Nf _ m' v) e)
| Nf Nb m v (Expr.app e₁ e₂) := Expr.app (subst m v e₁) (subst m v e₂)
| Nf Nb m v (Expr.pair e₁ e₂) := Expr.pair (subst m v e₁) (subst m v e₂)
| Nf Nb m v (Expr.π₁ e) := Expr.π₁ (subst m v e)
| Nf Nb m v (Expr.π₂ e) := Expr.π₂ (subst m v e)
-/

end Lam
