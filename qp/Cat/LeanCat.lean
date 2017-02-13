/- ----------------------------------------------------------------------------
Properties of LeanCat.
---------------------------------------------------------------------------- -/

import .basic
import .Cone

namespace qp
universe variables ℓobj ℓhom



/- ----------------------------------------------------------------------------
Limits.
---------------------------------------------------------------------------- -/

/-! #brief For certain type levels, LeanCat has all limits.
-/
definition LeanCat.HasAllLimits
    : HasAllLimits.{ℓobj ℓhom} LeanCat.{max 1 ℓobj ℓhom}
:= { limit
      := λ {B : Cat.{ℓobj ℓhom}} (F : B ⇉⇉ LeanCat.{max 1 ℓobj ℓhom})
         , { g : ∀ (b : [[B]]), F b // ∀ {b₁ b₂ : [[B]]} (f : b₁ →→ b₂), g b₂ = (F ↗ f) (g b₁) }
   , is_limit
      := λ {B : Cat.{ℓobj ℓhom}} (F : B ⇉⇉ LeanCat.{max 1 ℓobj ℓhom})
         , { is_cone := { proj := λ b g, g^.elt_of b
                        , triangle
                           := λ b₁ b₂ f
                              , begin
                                  dsimp, apply funext, intro g,
                                  apply g^.has_property
                                end
                        }
           , is_final := { final := λ cone, { mediate := λ c, ⟨ λ b, (cone b) c
                                                              , λ b₁ b₂ f, begin dsimp, rw cone^.is_cone^.triangle end
                                                              ⟩
                                            , factor := λ x, rfl
                                            }
                         , uniq
                            := λ cone h
                               , begin
                                   apply ConeHom.eq,
                                   apply funext, intro c,
                                   apply subtype.eq,
                                   dsimp,
                                   apply funext, intro x,
                                   rw h^.factor
                                 end
                         }
           }
   }



/- ----------------------------------------------------------------------------
Initial and final objects.
---------------------------------------------------------------------------- -/

/-! #brief poly_empty is an initial object in LeanCat.
-/
@[reducible] definition {ℓ} LeanCat.init : IsInit LeanCat.{ℓ} poly_empty.{ℓ}
:= { init := λ A, poly_empty.elim
   , uniq := λ A f, begin
                      apply funext, intro e,
                      exact poly_empty.elim e
                    end
   }

/-! #brief poly_unit is a final object in LeanCat.
-/
@[reducible] definition {ℓ} LeanCat.final : IsFinal LeanCat.{ℓ} poly_unit.{ℓ}
:= { final := λ A a, poly_unit.star
   , uniq := λ A f, begin
                      apply funext, intro a,
                      apply poly_unit.uniq
                    end
   }

end qp
