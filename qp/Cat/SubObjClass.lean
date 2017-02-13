/- ----------------------------------------------------------------------------
Subobject classifiers.
---------------------------------------------------------------------------- -/

import .basic
import .Cone
import .Pullback

namespace qp
universe variables ℓobj ℓhom



-- A subobject classifier.
structure SubObjClass (C : Cat.{ℓobj ℓhom})
    {t : [[C]]} (t_final : IsFinal C t)
    : Type (max 1 ℓobj ℓhom)
:= (Ω : [[C]])
   (true : t →→ Ω)
   (true_monic : Monic true)
   (char : ∀ {u x : [[C]]} (f : u →→ x) (f_monic : Monic f)
           , x →→ Ω)
   (char_pullback : ∀ {u x : [[C]]} (f : u →→ x) (f_monic : Monic f)
                    , IsPullback (char f f_monic) true f (t_final u))
   (char_uniq : ∀ {u x : [[C]]} (f : u →→ x) (f_monic : Monic f) (char' : x →→ Ω)
                  (ω : IsPullback char' true f (t_final u))
                , char' = char f f_monic)

end qp
