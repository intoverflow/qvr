/- ----------------------------------------------------------------------------
Dependent sums in LeanCat.
---------------------------------------------------------------------------- -/

import ..Cat
import .Pullback

namespace qp



/- ----------------------------------------------------------------------------
Dependent sums.
---------------------------------------------------------------------------- -/

/-! #brief The Lean categories have dependent sums.
-/
@[reducible] definition {ℓ} LeanCat.DepSumFun
    {T₀ T₁ : [[LeanCat.{ℓ}]]}
    (base : LeanCat^.hom T₀ T₁)
    : SliceCat LeanCat T₀ ⇉⇉ SliceCat LeanCat T₁
:= DepSumFun (@LeanCat.HasAllPullbacksAlong _ _ base)

/-! #brief The Lean categories have dependent sums.
-/
@[reducible] definition {ℓ} LeanCat.DepSum_BaseChange.Adj
    {T₀ T₁ : [[LeanCat.{ℓ}]]}
    (base : LeanCat^.hom T₀ T₁)
    : LeanCat.DepSumFun base ⊣ LeanCat.BaseChangeFun base
:= DepSum_BaseChange.Adj (@LeanCat.HasAllPullbacksAlong _ _ base)

end qp
