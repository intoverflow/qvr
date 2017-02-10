namespace list

/-! #brief list.nth, but without the option monad.
-/
@[reducible] definition {ℓ} get {A : Type ℓ}
    : ∀ (aa : list A) (idx : fin (length aa))
      , A
| [] (fin.mk idx ω) := begin apply false.rec, cases ω end
| (a :: aa) (fin.mk 0 ω) := a
| (a :: aa) (fin.mk (nat.succ idx) ω) := get aa { val := idx, is_lt := sorry }

end list
