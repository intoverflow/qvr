/- ----------------------------------------------------------------------------
Lambda calculus.
---------------------------------------------------------------------------- -/

import ..util
import ..Qvr

namespace qp
namespace Lam

open list

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

-- A notion of reduction for the lambda calculus.
structure Notion : Type
:= (guard : ∀ {Nf Nb : ℕ}, Expr Nf Nb → Prop)
   (guard_dec : ∀ {Nf Nb : ℕ} (e: Expr Nf Nb)
                , decidable (guard e))
   (rule : ∀ {Nf Nb : ℕ} (e : Expr Nf Nb)
             (ωe : guard e)
           , Expr Nf Nb)

attribute [instance] Notion.guard_dec

/-! #brief Compatible closure of the notions of reduction.
-/
inductive Step (NS : list Notion) : ∀ {Nf Nb : ℕ}, Expr Nf Nb → Expr Nf Nb → Type
| rule : ∀ {Nf Nb : ℕ} (e : Expr Nf Nb)
           (r : fin (length NS))
           (ωe : (get NS r)^.guard e)
         , Step e ((get NS r)^.rule e ωe)
| lam : ∀ {Nf Nb : ℕ} (e e' : Expr Nf (Nb+1))
          (s : Step e e')
        , Step (Expr.lam e) (Expr.lam e')
| app₁ : ∀ {Nf Nb : ℕ} (e₁ e₂ e₁' : Expr Nf Nb)
           (s : Step e₁ e₁')
         , Step (Expr.app e₁ e₂) (Expr.app e₁' e₂)
| app₂ : ∀ {Nf Nb : ℕ} (e₁ e₂ e₂' : Expr Nf Nb)
           (s : Step e₂ e₂')
         , Step (Expr.app e₁ e₂) (Expr.app e₁ e₂')
| pair₁ : ∀ {Nf Nb : ℕ} (e₁ e₂ e₁' : Expr Nf Nb)
            (s : Step e₁ e₁')
          , Step (Expr.pair e₁ e₂) (Expr.pair e₁' e₂)
| pair₂ : ∀ {Nf Nb : ℕ} (e₁ e₂ e₂' : Expr Nf Nb)
            (s : Step e₂ e₂')
          , Step (Expr.pair e₁ e₂) (Expr.pair e₁ e₂')
| π₁ : ∀ {Nf Nb : ℕ} (e e' : Expr Nf Nb)
         (s : Step e e')
       , Step (Expr.π₁ e) (Expr.π₁ e)
| π₂ : ∀ {Nf Nb : ℕ} (e e' : Expr Nf Nb)
         (s : Step e e')
       , Step (Expr.π₂ e) (Expr.π₂ e')

-- A boxed step.
structure BxStep (NS : list Notion) (Nf Nb : ℕ) : Type
:= (src : Expr Nf Nb)
   (dst : Expr Nf Nb)
   (step : Step NS src dst)

-- TODO: Fix docstring!
--/-! #brief Lifts a variable.
---/
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

/-! #brief can_beta is decidable.
-/
@[reducible] instance can_beta.decidable
    : ∀ {Nf Nb : ℕ} (e : Expr Nf Nb)
      , decidable (can_beta e)
| Nf Nb (Expr.unit) := decidable.is_false (λ ωe, begin cases ωe end)
| Nf Nb (Expr.fvar f) := decidable.is_false (λ ωe, begin cases ωe end)
| Nf Nb (Expr.bvar b) := decidable.is_false (λ ωe, begin cases ωe end)
| Nf Nb (Expr.lam e) := decidable.is_false (λ ωe, begin cases ωe end)
| Nf Nb (Expr.app (Expr.unit) e₂) := decidable.is_false (λ ωe, begin cases ωe end)
| Nf Nb (Expr.app (Expr.fvar f) e₂) := decidable.is_false (λ ωe, begin cases ωe end)
| Nf Nb (Expr.app (Expr.bvar b) e₂) := decidable.is_false (λ ωe, begin cases ωe end)
| Nf Nb (Expr.app (Expr.lam e₁) e₂) := decidable.is_true (can_beta.ω e₁ e₂)
| Nf Nb (Expr.app (Expr.app e₁ e₂) e₃) := decidable.is_false (λ ωe, begin cases ωe end)
| Nf Nb (Expr.app (Expr.pair e₁ e₂) e₃) := decidable.is_false (λ ωe, begin cases ωe end)
| Nf Nb (Expr.app (Expr.π₁ e₁) e₂) := decidable.is_false (λ ωe, begin cases ωe end)
| Nf Nb (Expr.app (Expr.π₂ e₁) e₂) := decidable.is_false (λ ωe, begin cases ωe end)
| Nf Nb (Expr.pair e₁ e₂) := decidable.is_false (λ ωe, begin cases ωe end)
| Nf Nb (Expr.π₁ e) := decidable.is_false (λ ωe, begin cases ωe end)
| Nf Nb (Expr.π₂ e) := decidable.is_false (λ ωe, begin cases ωe end)

/-! #brief Applies beta reduction on the head.
-/
@[reducible] definition rule_beta
    : ∀ {Nf Nb : ℕ} (e : Expr Nf Nb)
        (ωe : can_beta e)
      , Expr Nf Nb
| Nf Nb (Expr.app (Expr.lam e₁) e₂) ωe
:= subst e₁ e₂ { val := 0, is_lt := sorry } rfl
| Nf Nb e ωe := e

/-! #brief beta reduction as a notion of reduction.
-/
@[reducible] definition Notion.beta : Notion
:= { guard := @can_beta
   , guard_dec := @can_beta.decidable
   , rule := @rule_beta
   }

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

/-! #brief can_π₁ is decidable.
-/
@[reducible] instance can_π₁.decidable
    : ∀ {Nf Nb : ℕ} (e : Expr Nf Nb)
      , decidable (can_π₁ e)
| Nf Nb (Expr.unit) := decidable.is_false (λ ωe, begin cases ωe end)
| Nf Nb (Expr.fvar f) := decidable.is_false (λ ωe, begin cases ωe end)
| Nf Nb (Expr.bvar b) := decidable.is_false (λ ωe, begin cases ωe end)
| Nf Nb (Expr.lam e) := decidable.is_false (λ ωe, begin cases ωe end)
| Nf Nb (Expr.app e₁ e₂) := decidable.is_false (λ ωe, begin cases ωe end)
| Nf Nb (Expr.pair e₁ e₂) := decidable.is_false (λ ωe, begin cases ωe end)
| Nf Nb (Expr.π₁ (Expr.unit)) := decidable.is_false (λ ωe, begin cases ωe end)
| Nf Nb (Expr.π₁ (Expr.fvar f)) := decidable.is_false (λ ωe, begin cases ωe end)
| Nf Nb (Expr.π₁ (Expr.bvar b)) := decidable.is_false (λ ωe, begin cases ωe end)
| Nf Nb (Expr.π₁ (Expr.lam e)) := decidable.is_false (λ ωe, begin cases ωe end)
| Nf Nb (Expr.π₁ (Expr.app e₁ e₂)) := decidable.is_false (λ ωe, begin cases ωe end)
| Nf Nb (Expr.π₁ (Expr.pair e₁ e₂)) := decidable.is_true (can_π₁.ω e₁ e₂)
| Nf Nb (Expr.π₁ (Expr.π₁ e)) := decidable.is_false (λ ωe, begin cases ωe end)
| Nf Nb (Expr.π₁ (Expr.π₂ e)) := decidable.is_false (λ ωe, begin cases ωe end)
| Nf Nb (Expr.π₂ e) := decidable.is_false (λ ωe, begin cases ωe end)

/-! #brief Applies left projection on the head.
-/
@[reducible] definition rule_π₁
    : ∀ {Nf Nb : ℕ} (e : Expr Nf Nb)
        (ωe : can_π₁ e)
      , Expr Nf Nb
| Nf Nb (Expr.π₁ (Expr.pair e₁ e₂)) ωe := e₁
| Nf Nb e ωe := e

/-! #brief Left projection as a notion of reduction.
-/
@[reducible] definition Notion.π₁ : Notion
:= { guard := @can_π₁
   , guard_dec := @can_π₁.decidable
   , rule := @rule_π₁
   }

/-! #brief Guard for right projection.
-/
inductive can_π₂ {Nf Nb : ℕ} : Expr Nf Nb → Prop
| ω : ∀ (e₁ e₂ : Expr Nf Nb)
      , can_π₂ (Expr.π₂ (Expr.pair e₁ e₂))

/-! #brief can_π₂ is decidable.
-/
@[reducible] instance can_π₂.decidable
    : ∀ {Nf Nb : ℕ} (e : Expr Nf Nb)
      , decidable (can_π₂ e)
| Nf Nb (Expr.unit) := decidable.is_false (λ ωe, begin cases ωe end)
| Nf Nb (Expr.fvar f) := decidable.is_false (λ ωe, begin cases ωe end)
| Nf Nb (Expr.bvar b) := decidable.is_false (λ ωe, begin cases ωe end)
| Nf Nb (Expr.lam e) := decidable.is_false (λ ωe, begin cases ωe end)
| Nf Nb (Expr.app e₁ e₂) := decidable.is_false (λ ωe, begin cases ωe end)
| Nf Nb (Expr.pair e₁ e₂) := decidable.is_false (λ ωe, begin cases ωe end)
| Nf Nb (Expr.π₁ e) := decidable.is_false (λ ωe, begin cases ωe end)
| Nf Nb (Expr.π₂ (Expr.unit)) := decidable.is_false (λ ωe, begin cases ωe end)
| Nf Nb (Expr.π₂ (Expr.fvar f)) := decidable.is_false (λ ωe, begin cases ωe end)
| Nf Nb (Expr.π₂ (Expr.bvar b)) := decidable.is_false (λ ωe, begin cases ωe end)
| Nf Nb (Expr.π₂ (Expr.lam e)) := decidable.is_false (λ ωe, begin cases ωe end)
| Nf Nb (Expr.π₂ (Expr.app e₁ e₂)) := decidable.is_false (λ ωe, begin cases ωe end)
| Nf Nb (Expr.π₂ (Expr.pair e₁ e₂)) := decidable.is_true (can_π₂.ω e₁ e₂)
| Nf Nb (Expr.π₂ (Expr.π₁ e)) := decidable.is_false (λ ωe, begin cases ωe end)
| Nf Nb (Expr.π₂ (Expr.π₂ e)) := decidable.is_false (λ ωe, begin cases ωe end)

/-! #brief Applies right projection on the head.
-/
@[reducible] definition rule_π₂
    : ∀ {Nf Nb : ℕ} (e : Expr Nf Nb)
        (ωe : can_π₂ e)
      , Expr Nf Nb
| Nf Nb (Expr.π₂ (Expr.pair e₁ e₂)) ωe := e₂
| Nf Nb e ωe := e

/-! #brief Right projection as a notion of reduction.
-/
@[reducible] definition Notion.π₂ : Notion
:= { guard := @can_π₂
   , guard_dec := @can_π₂.decidable
   , rule := @rule_π₂
   }

/-! #brief The standard rules of lambda calculus.
-/
@[reducible] definition Notion.std : list Notion
:= Notion.beta :: Notion.π₁ :: Notion.π₂ :: nil

/- #brief The quiver of single step reductions for lambda calculus.
-/
@[reducible] definition RedQvr (NS : list Notion) (Nf Nb : ℕ) : Qvr
:= { vtx := Expr Nf Nb
   , arr := BxStep NS Nf Nb
   , src := BxStep.src
   , dst := BxStep.dst
   }

/-! #brief The category of traces of reductions for lambda calculus.
-/
@[reducible] definition RedCat (NS : list Notion) (Nf Nb : ℕ) : Cat
:= FreeCat (RedQvr NS Nf Nb)

end Lam
end qp
