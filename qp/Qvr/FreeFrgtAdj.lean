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

/-
/-! #brief The adjunction between FreeCatFun and FrgtQvrFun.
-/
@[reducible] definition FreeCat_FrgtQvr_Adj
    : @Adj QvrCat.{ℓobj ((max ℓobj ℓhom) + 1)}
           CatCat.{ℓobj ((max ℓobj ℓhom) + 1)}
           FreeCatFun
           FrgtQvrFun
:= { counit := sorry
   , unit := sorry
   , id_left := sorry
   , id_right := sorry
   }
-/


/- ----------------------------------------------------------------------------
Free adjoints (via FreeCatFun and FrgtQvrFun).
---------------------------------------------------------------------------- -/

/-! #brief Helper for casting.
-/
@[simp] theorem FreeCat_FrgtQvr_Adj.free_adjoint.hom.cast
    {Q : Qvr} {C : Cat}
    {F : Q ⇒⇒ FrgtQvr C}
    : ∀ {m n : ‖Q‖} {e : Qvr.BxArr m n}
      , (F ↘ e^.arr)^.dom →→ (F ↘ e^.arr)^.codom
         = F m →→ F n
| .([arr⟩) .(⟨arr]) (Qvr.BxArr.mk arr (eq.refl .([arr⟩)) (eq.refl .(⟨arr])))
:= begin dsimp, rw [-F^.src, -F^.dst] end

/-! #brief The action of the free adjoint on a hom.
-/
@[reducible] definition FreeCat_FrgtQvr_Adj.free_adjoint.hom
    {Q : Qvr} {C : Cat}
    (F : Q ⇒⇒ FrgtQvr C)
    : ∀ {x y : [[FreeCat Q]]} (f : (FreeCat Q)^.hom x y)
      , F x →→ F y
| x y f
:= begin
     dsimp at f,
     induction f,
     { apply Cat.id },
     { exact ih_1 ∘∘ cast FreeCat_FrgtQvr_Adj.free_adjoint.hom.cast (F ↘ e^.arr)^.hom }
   end

/-! #brief Helper lemma for computing FreeCat_FrgtQvr_Adj.free_adjoint.hom.
-/
@[simp] theorem FreeCat_FrgtQvr_Adj.free_adjoint.hom.step
    {Q : Qvr} {C : Cat}
    (F : Q ⇒⇒ FrgtQvr C)
    {x₁ x₂ x₃ : ‖Q‖} {e : Qvr.BxArr x₁ x₂} {es : x₂ ↝↝ x₃}
    : FreeCat_FrgtQvr_Adj.free_adjoint.hom F (FreeCat.Hom.step x₁ x₂ x₃ e es)
       = FreeCat_FrgtQvr_Adj.free_adjoint.hom F es
          ∘∘ cast FreeCat_FrgtQvr_Adj.free_adjoint.hom.cast (F ↘ e^.arr)^.hom
:= rfl

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
             dsimp at f,
             induction f,
             { exact sorry
            --    simp,
            --    rw FreeCat.Hom.comp_id_right,
            --    rw FreeCat_FrgtQvr_Adj.free_adjoint.hom_id,
            --    rw Cat.circ_id_right
             },
             { exact sorry
            --    simp,
            --    rw FreeCat.Hom.comp.step,
            --    repeat { rw FreeCat_FrgtQvr_Adj.free_adjoint.hom.step },
            --    rw ih_1,
            --    rw Cat.circ_assoc
             }
           end
   }

end qp
