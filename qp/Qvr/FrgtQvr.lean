/- ----------------------------------------------------------------------------
Free categories.
---------------------------------------------------------------------------- -/

import .basic

namespace qp
universe variables ℓobj ℓhom ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂ ℓobj₃ ℓhom₃



/- ----------------------------------------------------------------------------
The quiver underlying a category.
---------------------------------------------------------------------------- -/

/-! #brief The quiver underlying a category.
-/
@[reducible] definition FrgtQvr (C : Cat.{ℓobj ℓhom})
    : Qvr.{ℓobj ((max ℓobj ℓhom) + 1)}
:= { vtx := [[C]]
   , arr := Cat.BxHom C
   , src := Cat.BxHom.dom
   , dst := Cat.BxHom.codom
   }


/- ----------------------------------------------------------------------------
The quiver morphism underlying a functor.
---------------------------------------------------------------------------- -/

/-! #brief The quiver morphism underlying a functor.
-/
@[reducible] definition FrgtQvr.FrgtMor {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    (F : C ⇉⇉ D)
    : FrgtQvr C ⇒⇒ FrgtQvr D
:= { vtx := Fun.obj F
   , arr := λ f, { dom := F f^.dom
                 , codom := F f^.codom
                 , hom := F ↗ f^.hom
                 }
   , src := λ f, by simp
   , dst := λ f, by simp
   }

/-! #brief FrgtQvr.FrgtFun maps the identity functor to the identity morphism.
-/
@[simp] theorem FrgtQvr.FrgtMor.id {C : Cat.{ℓobj ℓhom}}
    : FrgtQvr.FrgtMor (Fun.id C) = Qvr.Mor.id (FrgtQvr C)
:= begin
     apply Qvr.Mor.eq,
     { intro x, apply rfl },
     { intro f, cases f, apply rfl }
   end

/-! #brief FrgtQvr.FrgtMor distributes over composition.
-/
@[simp] theorem FrgtQvr.FrgtMor.comp {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}} {D : Cat.{ℓobj₃ ℓhom₃}}
    {G : C ⇉⇉ D} {F : B ⇉⇉ C}
    : FrgtQvr.FrgtMor (G □□ F) = FrgtQvr.FrgtMor G ◯◯ FrgtQvr.FrgtMor F
:= begin
     apply Qvr.Mor.eq,
     { intro x, apply rfl },
     { intro f, cases f, apply rfl }
   end


/- ----------------------------------------------------------------------------
The forgetful functor yielding the quiver underlying a category.
---------------------------------------------------------------------------- -/

/-! #brief The forgetful functor yielding the quiver underlying a category.
-/
@[reducible] definition FrgtQvrFun
    : CatCat.{ℓobj ℓhom} ⇉⇉ QvrCat.{ℓobj ((max ℓobj ℓhom) + 1)}
:= { obj := FrgtQvr
   , hom := @FrgtQvr.FrgtMor
   , hom_id := @FrgtQvr.FrgtMor.id
   , hom_circ := @FrgtQvr.FrgtMor.comp
   }


end qp
