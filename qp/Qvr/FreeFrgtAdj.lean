/- ----------------------------------------------------------------------------
The adjunction between FreeCatFun and FrgtQvrFun.
---------------------------------------------------------------------------- -/

import .FreeCat
import .FrgtQvr

namespace qp
universe variables ℓobj ℓhom



/- ----------------------------------------------------------------------------
The adjunction between FreeCatFun and FrgtQvrFun.
---------------------------------------------------------------------------- -/

/-! #brief The adjunction between FreeCatFun and FrgtQvrFun.
-/
@[reducible] definition FreeCat_FrgtQvr_Adj
    : @Adj QvrCat.{ℓobj (max 1 ℓobj ℓhom)}
           CatCat.{ℓobj (max 1 ℓobj ℓhom)}
           FreeCatFun
           FrgtQvrFun
:= { counit := sorry
   , unit := sorry
   , id_left := sorry
   , id_right := sorry
   }



/- ----------------------------------------------------------------------------
Free adjoints (via FreeCatFun and FrgtQvrFun).
---------------------------------------------------------------------------- -/

/-! #brief The action of the free adjoint on a hom.
-/
@[reducible] definition FreeCat_FrgtQvr_Adj.free_adjoint.hom
    {Q : Qvr} {C : Cat}
    (F : Q ⇒⇒ FrgtQvr C)
    : ∀ {x y : [[FreeCat Q]]} (f : (FreeCat Q)^.hom x y)
      , F x →→ F y
| x y f
:= begin
     induction f,
     { apply Cat.id },
     { cases e,
       refine ih_1 ∘∘ cast _ (F ↘ arr)^.hom,
       subst src, subst dst,
       dsimp,
       rw [-F^.src, -F^.dst]
     }
   end

/-! #brief The action of the free adjoint on an identity hom.
-/
theorem FreeCat_FrgtQvr_Adj.free_adjoint.hom_id
    {Q : Qvr} {C : Cat}
    {F : Q ⇒⇒ FrgtQvr C}
    {v : [[FreeCat Q]]}
    : FreeCat_FrgtQvr_Adj.free_adjoint.hom F (FreeCat.Hom.id v) = ⟨⟨ F v ⟩⟩
:= rfl

/-! #brief Constructing a functor out of a free category.
-/
@[reducible] definition FreeCat_FrgtQvr_Adj.free_adjoint
    {Q : Qvr} {C : Cat}
    (F : Q ⇒⇒ FrgtQvr C)
    : FreeCat Q ⇉⇉ C
:= { obj := λ x, F x
   , hom := λ x y f, FreeCat_FrgtQvr_Adj.free_adjoint.hom F f
   , hom_id := λ x, FreeCat_FrgtQvr_Adj.free_adjoint.hom_id
   , hom_circ
      := λ x y z g f
         , begin
             induction f,
             { simp,
               rw FreeCat.Hom.comp_id_right,
               rw FreeCat_FrgtQvr_Adj.free_adjoint.hom_id,
               rw Cat.circ_id_right
             },
             { exact sorry
             }
           end
   }

end qp
