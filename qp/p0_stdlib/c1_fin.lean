/- -----------------------------------------------------------------------
Facts about (fin n).
----------------------------------------------------------------------- -/

namespace qp
namespace stdaux

/-! #brief Zero is in fin (nat.succ n).
-/
definition fin.zero {n : ℕ}
    : fin (nat.succ n)
:= { val := 0
   , is_lt := nat.zero_lt_succ n
   }

/-! #brief One is in fin (nat.succ (nat.succ n)).
-/
definition fin.one {n : ℕ}
    : fin (nat.succ (nat.succ n))
:= { val := 1
   , is_lt := begin
                apply nat.succ_lt_succ,
                apply nat.zero_lt_succ
              end
   }

/-! #brief fin 0 is uninhabited.
-/
definition {ℓ} fin.zero_elim {A : Sort ℓ}
    : fin 0 → A
| (fin.mk n ω) := false.rec A begin cases ω end

/-! #brief fin 1 is uniquely inhabited.
-/
definition fin.zero_uniq
    : ∀ (n : fin 1)
      , n = fin.zero
| (fin.mk 0 ω) := rfl
| (fin.mk (nat.succ n) ω) := begin cases ω, cases a end

end stdaux
end qp
