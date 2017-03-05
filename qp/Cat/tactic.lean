/- ----------------------------------------------------------------------------
Tactics for working in categories.
---------------------------------------------------------------------------- -/

import .basic



namespace qp
open list
open tactic

definition when {m : Type → Type}
    [m_monad_fail : monad_fail m]
    (P : Prop)
    [P_decidable : decidable P]
    (act : m unit)
    : m unit
:= do if P then act else return unit.star

meta def is_eq_of_homs : expr → option (expr × expr × expr)
| ``(@eq (Cat.hom %%C %%x %%y) %%left %%right) := option.some (C, left, right)
| _ := option.none

meta def is_hom : expr → option (expr × expr × expr)
| ``(Cat.hom %%C %%x %%y) := option.some (C, x, y)
| _                       := option.none

meta structure boxed_circ
:= (cat : expr)
   (x : expr)
   (y : expr)
   (z : expr)
   (g : expr)
   (f : expr)

meta def is_circ : expr → option boxed_circ
| ``(@Cat.circ %%C %%x %%y %%z %%g %%f)
:= option.some { cat := C, x := x, y := y, z := z, g := g, f := f}
| _
:= option.none

meta def to_circ_list : expr → list expr
| ``(@Cat.circ %%C %%x %%y %%z %%g %%f) := (to_circ_list f) ++ (to_circ_list g)
| e := [e]

meta def of_circ_list : expr → list expr → tactic expr
| cat [] := fail "of_circ_list: empty list"
| cat [e] := return e
| cat (f :: fs) := do lhs <- of_circ_list cat fs
                    , to_expr `(Cat.circ %%cat %%lhs %%f)

meta def indent : ℕ → string
| nat.zero := ""
| (nat.succ n) := " " ++ indent n

-- Indicates that g ∘∘ f is already normal.
meta structure circ_normalize.is_normal
:= (g : expr)
   (f : expr)

-- rw gives equality to (g ∘∘ f), which furthermore is in normal form.
meta structure circ_normalize.rhs_singleton
:= (g : expr)
   (f : expr)
   (rw : expr)

meta inductive circ_normalize.ret
| singleton : circ_normalize.ret
| already_normal : circ_normalize.is_normal → circ_normalize.ret
| needs_rw : circ_normalize.rhs_singleton → circ_normalize.ret

meta def circ_normalize.expr : ℕ → expr → tactic circ_normalize.ret
:= λ d e
   , do pp_e <- pp e
      , match is_circ e with
          | option.none
             := do trace (indent d ++ "singleton: " ++ to_string e)
                 , return circ_normalize.ret.singleton
          | (option.some e_circ)
             := do trace (indent d ++ "normalizing " ++ to_string pp_e)
                 , on_f <- circ_normalize.expr (nat.succ d) e_circ^.f
                 , match on_f with
                     | circ_normalize.ret.singleton
                        := do trace (indent d ++ "rhs singleton")
                            , on_g <- circ_normalize.expr (nat.succ d) e_circ^.g
                            , match on_g with
                                | circ_normalize.ret.singleton
                                   := do trace (indent d ++ "lhs singleton")
                                       , return (circ_normalize.ret.already_normal { g := e_circ^.g, f := e_circ^.f })
                                | circ_normalize.ret.already_normal g_normal
                                   := do trace (indent d ++ "lhs normal")
                                       , return (circ_normalize.ret.already_normal { g := e_circ^.g, f := e_circ^.f })
                                | circ_normalize.ret.needs_rw g_needs_rw
                                   := do trace (indent d ++ "lhs needs normal xx")
                                       , rw <- to_expr `(congr_arg (λ g', g' ∘∘ %%e_circ^.f) %%g_needs_rw^.rw)
                                       , g' <- to_expr `(Cat.circ %%e_circ^.cat %%g_needs_rw^.g %%g_needs_rw^.f)
                                       , return (circ_normalize.ret.needs_rw { g := g', f := e_circ^.f, rw := rw })
                              end
                     | circ_normalize.ret.already_normal f_normal
                        := do trace (indent d ++ "rhs normal")
                            , rw_assoc <- to_expr `(Cat.circ_assoc %%e_circ^.cat)
                              -- rw_assoc : e_circ^.g ∘∘ (f_normal^.g ∘∘ f_normal^.f)
                              --             = (e_circ^.g ∘∘ f_normal^.g) ∘∘ f_normal^.f
                            , g' <- to_expr `(Cat.circ %%e_circ^.cat %%e_circ^.g %%f_normal^.g)
                            , on_g' <- circ_normalize.expr (nat.succ d) g'
                            , match on_g' with
                                | circ_normalize.ret.singleton
                                   := fail "impossible case: g' should not be a singleton"
                                | circ_normalize.ret.already_normal g'_normal
                                   := do trace (indent d ++ "lhs normal")
                                       , return (circ_normalize.ret.needs_rw { g := g', f := f_normal^.f, rw := rw_assoc })
                                | circ_normalize.ret.needs_rw g'_needs_rw
                                   := do trace (indent d ++ "lhs needs normal")
                                       , g'' <- to_expr `(Cat.circ %%e_circ^.cat %%g'_needs_rw^.g %%g'_needs_rw^.f)
                                       , rw_g' <- to_expr `(congr_arg (λ g'', g'' ∘∘ %%f_normal^.f) %%g'_needs_rw^.rw)
                                         -- rw_g' : (e_circ^.g ∘∘ f_normal^.g) ∘∘ f_normal^.f
                                         --          = g'' ∘∘ f_normal^.f
                                       , rw <- to_expr `(eq.trans %%rw_assoc %%rw_g')
                                       , return (circ_normalize.ret.needs_rw { g := g'', f := f_normal^.f, rw := rw })
                              end
                     | circ_normalize.ret.needs_rw f_needs_rw
                        := do trace (indent d ++ "rhs needs normal")
                            , rw_f <- to_expr `(congr_arg (λ f', %%e_circ^.g ∘∘ f') %%f_needs_rw^.rw)
                              -- rw_f : e_circ^.g ∘∘ e_circ^.f
                              --          = e_circ^.g ∘∘ (f_needs_rw^.g ∘∘ f_needs_rw^.f)
                            , rw_assoc <- to_expr `(eq.trans %%rw_f (Cat.circ_assoc %%e_circ^.cat))
                              -- rw_assoc : e_circ^.g ∘∘ e_circ^.f
                              --             = (e_circ^.g ∘∘ f_needs_rw^.g) ∘∘ f_needs_rw^.f
                            , g' <- to_expr `(Cat.circ %%e_circ^.cat %%e_circ^.g %%f_needs_rw^.g)
                            , on_g' <- circ_normalize.expr (nat.succ d) g'
                            , match on_g' with
                                | circ_normalize.ret.singleton
                                   := fail "impossible case: g' should not be a singleton"
                                | circ_normalize.ret.already_normal g'_normal
                                   := do trace (indent d ++ "lhs normal")
                                       , return (circ_normalize.ret.needs_rw { g := g', f := f_needs_rw^.f, rw := rw_assoc })
                                | circ_normalize.ret.needs_rw g'_needs_rw
                                   := do trace (indent d ++ "lhs needs normal")
                                       , g'' <- to_expr `(Cat.circ %%e_circ^.cat %%g'_needs_rw^.g %%g'_needs_rw^.f)
                                       , rw_g' <- to_expr `(congr_arg (λ g'', g'' ∘∘ %%f_needs_rw^.f) %%g'_needs_rw^.rw)
                                         -- rw_g' : (e_circ^.g ∘∘ f_needs_rw^.g) ∘∘ f_needs_rw^.f
                                         --          = (g'_needs_rw^.g ∘∘ g'_needs_rw^.f) ∘∘ f_needs_rw^.f
                                       , rw <- to_expr `(eq.trans %%rw_assoc %%rw_g')
                                       , return (circ_normalize.ret.needs_rw { g := g'', f := f_needs_rw^.f, rw := rw })
                              end
                   end
        end

meta def circ_normalize (cat : expr) (n : name) (e : expr) : tactic expr
:= do e_flat <- of_circ_list cat (to_circ_list e)
    , eq_ty <- to_expr `(%%e = %%e_flat)
    , pr <- circ_normalize.expr 0 e
    , match pr with
        | circ_normalize.ret.singleton
           := to_expr `(rfl)
        | circ_normalize.ret.already_normal g_normal
           := to_expr `(rfl)
        | circ_normalize.ret.needs_rw needs_rw
           := do nam <- get_unused_name n option.none
               , definev nam eq_ty needs_rw^.rw
               , get_local nam
      end

meta def solve_assoc : tactic unit
:= do t <- target
    , (cat, left, right) <- is_eq_of_homs t
    , trace "--left--"
    , left_norm <- circ_normalize cat `lhs left
    , trace "--right--"
    , right_norm <- circ_normalize cat `rhs right
    , to_expr `(eq.trans %%left_norm (eq.symm %%right_norm)) >>= exact



variables (C : Cat) (x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ : [[C]])
                    (f₁ : x₁ →→ x₂)
                    (f₂ : x₂ →→ x₃)
                    (f₃ : x₃ →→ x₄)
                    (f₄ : x₄ →→ x₅)
                    (f₅ : x₅ →→ x₆)
                    (f₆ : x₆ →→ x₇)
                    (f₇ : x₇ →→ x₈)
                    (f₈ : x₈ →→ x₉)

-- example : f₁ = f₁
-- := by solve_assoc

-- example : f₂ ∘∘ f₁ = f₂ ∘∘ f₁
-- := by solve_assoc

-- example : f₃ ∘∘ f₂ ∘∘ f₁ = f₃ ∘∘ f₂ ∘∘ f₁
-- := by solve_assoc

-- example : f₃ ∘∘ (f₂ ∘∘ f₁) = f₃ ∘∘ f₂ ∘∘ f₁
-- := by solve_assoc

-- example : f₄ ∘∘ f₃ ∘∘ f₂ ∘∘ f₁ = f₄ ∘∘ f₃ ∘∘ f₂ ∘∘ f₁
-- := by solve_assoc

-- example : f₄ ∘∘ f₃ ∘∘ (f₂ ∘∘ f₁) = f₄ ∘∘ f₃ ∘∘ f₂ ∘∘ f₁
-- := by solve_assoc

-- example : f₄ ∘∘ (f₃ ∘∘ f₂) ∘∘ f₁ = f₄ ∘∘ f₃ ∘∘ f₂ ∘∘ f₁
-- := by solve_assoc

-- example : f₄ ∘∘ (f₃ ∘∘ (f₂ ∘∘ f₁)) = f₄ ∘∘ f₃ ∘∘ f₂ ∘∘ f₁
-- := by solve_assoc

-- example : f₄ ∘∘ (f₃ ∘∘ f₂ ∘∘ f₁) = f₄ ∘∘ f₃ ∘∘ f₂ ∘∘ f₁
-- := by solve_assoc

-- example : f₈ ∘∘ ((f₇ ∘∘ (f₆ ∘∘ f₅) ∘∘ (f₄ ∘∘ (f₃ ∘∘ f₂))) ∘∘ f₁)
--            = f₈ ∘∘ ((f₇ ∘∘ (f₆ ∘∘ f₅)) ∘∘ ((f₄ ∘∘ f₃) ∘∘ (f₂ ∘∘ f₁)))
-- := by solve_assoc

-- example : f₈ ∘∘ f₇ ∘∘ f₆ ∘∘ f₅ ∘∘ f₄ ∘∘ f₃ ∘∘ f₂ ∘∘ f₁
--            = f₈ ∘∘ f₇ ∘∘ f₆ ∘∘ f₅ ∘∘ f₄ ∘∘ f₃ ∘∘ f₂ ∘∘ f₁
-- := by solve_assoc


end qp
