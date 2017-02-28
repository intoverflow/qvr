/- ----------------------------------------------------------------------------
Pullbacks in LeanCat.
---------------------------------------------------------------------------- -/

import ..Cat

namespace qp



/- ----------------------------------------------------------------------------
Pullbacks.
---------------------------------------------------------------------------- -/

/-! #brief The Lean categories have all pullbacks.
-/
@[reducible] definition {ℓ} LeanCat.HasAllPullbacks
    : HasAllPullbacks LeanCat.{ℓ}
:= λ A B Z ga gb
   , @Pullback.show LeanCat.{ℓ} A B Z ga gb
      { ab : A × B // ga ab^.fst = gb ab^.snd }
      (λ ab, ab^.elt_of^.fst)
      (λ ab, ab^.elt_of^.snd)
      (λ cone cn, { elt_of := { fst := cone^.proj CoSpanCat.Obj.a cn
                              , snd := cone^.proj CoSpanCat.Obj.b cn
                              }
                  , has_property := begin dsimp, exact sorry end
                  })
      begin apply funext, intro x, apply x^.has_property end
      (λ cone, rfl)
      (λ cone, rfl)
      (λ cone h, begin apply funext, intro cn, dsimp, exact sorry end)

/-! #brief The Lean categories have all pullbacks along all homs.
-/
@[reducible] definition {ℓ} LeanCat.HasAllPullbacksAlong
    {T₀ T₁ : [[LeanCat.{ℓ}]]}
    (base : LeanCat^.hom T₀ T₁)
    : HasAllPullbacksAlong LeanCat base
:= @HasAllPullbacks.HasAllPullbacksAlong _ @LeanCat.HasAllPullbacks _ _ base

/-! #brief The Lean categories have base change functors.
-/
@[reducible] definition {ℓ} LeanCat.BaseChangeFun
    {T₀ T₁ : [[LeanCat.{ℓ}]]}
    (base : LeanCat^.hom T₀ T₁)
    : SliceCat LeanCat T₁ ⇉⇉ SliceCat LeanCat T₀
:= BaseChangeFun (@LeanCat.HasAllPullbacksAlong _ _ base)


end qp
