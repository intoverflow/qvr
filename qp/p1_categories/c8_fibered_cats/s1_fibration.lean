/- -----------------------------------------------------------------------
Fibrations.
----------------------------------------------------------------------- -/

import ..c1_basic
import ..c2_limits
import ..c3_wtypes
import ..c4_topoi
import ..c7_cat_of_cats

namespace qp

open stdaux

universe variables ℓobjb ℓhomb ℓobj ℓhom



/- -----------------------------------------------------------------------
Cartesian homs.
----------------------------------------------------------------------- -/

/-! #brief A cartesian hom.
-/
structure CartesianHom {E : Cat.{ℓobj ℓhom}} {B : Cat.{ℓobjb ℓhomb}}
    (P : Fun E B)
    {e₁ e₂ : E^.obj} (φ : E^.hom e₁ e₂)
:= (char : ∀ {e₀ : E^.obj} (ψ : E^.hom e₀ e₂)
             (g : B^.hom (P^.obj e₀) (P^.obj e₁))
             (ω : P^.hom φ ∘∘ g = P^.hom ψ)
           , E^.hom e₀ e₁)
   (comm : ∀ {e₀ : E^.obj} (ψ : E^.hom e₀ e₂)
             (g : B^.hom (P^.obj e₀) (P^.obj e₁))
             (ω : P^.hom φ ∘∘ g = P^.hom ψ)
           , ψ = φ ∘∘ char ψ g ω)
   (char_im : ∀ {e₀ : E^.obj} (ψ : E^.hom e₀ e₂)
                (g : B^.hom (P^.obj e₀) (P^.obj e₁))
                (ω : P^.hom φ ∘∘ g = P^.hom ψ)
              , P^.hom (char ψ g ω) = g)
   (uniq : ∀ {e₀ : E^.obj} (ψ : E^.hom e₀ e₂)
             (g : B^.hom (P^.obj e₀) (P^.obj e₁))
             (ω : P^.hom φ ∘∘ g = P^.hom ψ)
             (char' : E^.hom e₀ e₁)
             (ωcomm : ψ = φ ∘∘ char')
             (ωim : P^.hom char' = g)
           , char' = char ψ g ω)

/-! #brief A cartesian lift.
-/
structure CartesianLift {E : Cat.{ℓobj ℓhom}} {B : Cat.{ℓobjb ℓhomb}}
    (P : Fun E B)
    {b : B^.obj} {e : E^.obj} (f : B^.hom b (P^.obj e))
    : Type (max ℓobj ℓhom ℓobjb ℓhomb)
:= (obj : E^.obj)
   (obj_im : P^.obj obj = b)
   (hom : E^.hom obj e)
   (hom_im : P^.hom hom = f ∘∘ cast_hom obj_im)
   (hom_cart : CartesianHom P hom)



/- -----------------------------------------------------------------------
Fibrations and cloven functors.
----------------------------------------------------------------------- -/

/-! #brief A fibration.
-/
class Fibration {E : Cat.{ℓobj ℓhom}} {B : Cat.{ℓobjb ℓhomb}}
    (P : Fun E B)
    : Type (max ℓobj ℓhom ℓobjb ℓhomb)
:= (lift : ∀ {b : B^.obj} {e : E^.obj} (f : B^.hom b (P^.obj e))
           , MerelyExists (CartesianLift P f))

/-! #brief A cloven functor.
-/
structure Cloven {E : Cat.{ℓobj ℓhom}} {B : Cat.{ℓobjb ℓhomb}}
    (P : Fun E B)
    : Type (max ℓobj ℓhom ℓobjb ℓhomb)
:= (lift : ∀ {b : B^.obj} {e : E^.obj} (f : B^.hom b (P^.obj e))
           , CartesianLift P f)

/-! #brief Every cloven functor is a fibration.
-/
definition Cloven.Fibration {E : Cat.{ℓobj ℓhom}} {B : Cat.{ℓobjb ℓhomb}}
    (P : Fun E B)
    (P_Cloven : Cloven P)
    : Fibration P
:= { lift := λ b e f, MerelyExists.intro (P_Cloven^.lift f)}

/-! #brief With the axiom of choice, every fibration is cloven.
-/
noncomputable definition Fibration.Cloven {E : Cat.{ℓobj ℓhom}} {B : Cat.{ℓobjb ℓhomb}}
    (P : Fun E B)
    [P_Fibration : Fibration P]
    : Cloven P
:= { lift := λ b e f, MerelyExists.choice (Fibration.lift f)}



/- -----------------------------------------------------------------------
The codomain fibration.
----------------------------------------------------------------------- -/

/-! #brief The codomain fibration.
-/
definition CodomFib (C : Cat.{ℓobj ℓhom})
    : Fun (ArrCat C) C
:= { obj := λ arr, arr^.codom
   , hom := λ arr₁ arr₂ f, f^.hom_codom
   , hom_id := λ arr₁, rfl
   , hom_circ := λ arr₁ arr₂ arr₃ g f, rfl
   }

/-! #brief If a category has pullbacks, CodomFib has Cartesian lifts.
-/
definition CodomFib.CartesianLift (C : Cat.{ℓobj ℓhom})
    [C_HasAllPullbacks : HasAllPullbacks C]
    {b : C^.obj} {e : (ArrCat C)^.obj} (f : C^.hom b ((CodomFib C)^.obj e))
    : CartesianLift (CodomFib C) f
:= { obj := { dom := pullback C (f ↗→ e^.hom ↗→↗)
            , codom := b
            , hom := pullback.π C (f ↗→ e^.hom ↗→↗) (@fin_of 1 0)
            }
   , obj_im := rfl
   , hom := { hom_dom := pullback.π C (f ↗→ e^.hom ↗→↗) (@fin_of 0 1)
            , hom_codom := f
            , comm := by apply pullback.π_comm C (f ↗→ e^.hom ↗→↗) (@fin_of 1 0) (@fin_of 0 1)
            }
   , hom_im := eq.symm C^.circ_id_right
   , hom_cart
      := let pcone : ∀ (e₀ : Arr C)
                       (ψ : ArrHom C e₀ e)
                       (g : C^.hom e₀^.codom b)
                       (ω : f ∘∘ g = ψ^.hom_codom)
                     , PullbackCone C (f↗→(e^.hom)↗→↗)
                  := λ e₀ ψ g ω
                     , PullbackCone.mk (f↗→(e^.hom)↗→↗) e₀^.dom
                                  (ψ^.hom_codom ∘∘ e₀^.hom)
                                  ((g ∘∘ e₀^.hom) ↗← ψ^.hom_dom ↗←↗)
                                  begin
                                    apply HomsList.eq, { rw [C^.circ_assoc, ω] },
                                    apply HomsList.eq, { exact ψ^.comm },
                                    trivial
                                  end
         in { char := λ e₀ ψ (g : C^.hom e₀^.codom b) (ω : f ∘∘ g = ψ^.hom_codom)
                      , { hom_dom := pullback.univ C (f↗→(e^.hom)↗→↗) (pcone e₀ ψ g ω)
                        , hom_codom := g
                        , comm := pullback.univ.mediates C (f↗→(e^.hom)↗→↗) (pcone e₀ ψ g ω) (@fin_of 1 0)
                        }
            , comm := λ e₀ ψ (g : C^.hom e₀^.codom b) (ω : f ∘∘ g = ψ^.hom_codom)
                      , ArrHom.eq
                         sorry
                         (eq.trans (eq.symm ω) rfl)
            , char_im := λ e₀ ψ (g : C^.hom e₀^.codom b) (ω : f ∘∘ g = ψ^.hom_codom)
                         , rfl
            , uniq := λ e₀ ψ (g : C^.hom e₀^.codom b) (ω : f ∘∘ g = ψ^.hom_codom)
                        char' ωcomm ωim
                      , ArrHom.eq
                          (pullback.univ.uniq C (f↗→(e^.hom)↗→↗) (pcone e₀ ψ g ω)
                            char'^.hom_dom
                            (λ n, begin
                                    cases n with n ωn,
                                    cases n with n,
                                    { exact sorry },
                                    cases n with n,
                                    { exact sorry },
                                    cases ωn with _ ωn,
                                    cases ωn with _ ωn,
                                    cases ωn
                                  end)
                            begin
                              exact sorry
                            end)
                          ωim
         }
   }


/-! #brief If a category has pullbacks, CodomFib is cloven.
-/
definition CodomFib.Cloven (C : Cat.{ℓobj ℓhom})
    [C_HasAllPullbacks : HasAllPullbacks C]
    : Cloven (CodomFib C)
:= { lift := λ b e f, CodomFib.CartesianLift C f
   }

/-! #brief If a category has pullbacks. CodomFib is a fibration.
-/
instance CodomFib.Fibration (C : Cat.{ℓobj ℓhom})
    [C_HasAllPullbacks : HasAllPullbacks C]
    : Fibration (CodomFib C)
:= Cloven.Fibration (CodomFib C) (CodomFib.Cloven C)



/- -----------------------------------------------------------------------
Fibrations are Conduché.
----------------------------------------------------------------------- -/

-- /-! #brief Fibrations can factorize.
-- -/
-- definition Fibration.factorize {E : Cat.{ℓobj ℓhom}} {B : Cat.{ℓobjb ℓhomb}}
--     (P : Fun E B)
--     (P_Fibration : Fibration P)
--     {a c : ⟦E⟧} (f : ⟦E : a →→ c⟧) {b : ⟦B⟧} (h : ⟦B : b →→ P^.obj c⟧)
--     (g : ⟦B : P^.obj a →→ b⟧) (ω : P^.hom f = h ∘∘ g)
--     : ConducheFact P f h g ω
-- := let cart := (P_Fibration^.lift h)^.hom_cart
-- in let g' := cast_hom (eq.symm (P_Fibration^.lift h)^.obj_im) ∘∘ g
-- in let ωchar : P^.hom ((P_Fibration^.lift h)^.hom) ∘∘ g' = P^.hom f
--             := begin
--                  rw (P_Fibration^.lift h)^.hom_im,
--                  refine eq.trans _ (eq.symm ω),
--                  rw B^.circ_assoc,
--                  apply Cat.circ.congr_left,
--                  rw -B^.circ_assoc,
--                  rw cast_hom.circ,
--                  rw cast_hom.simp,
--                  exact B^.circ_id_right
--                end
-- in ConducheFact.mk ω
--     (P_Fibration^.lift h)^.obj
--     (P_Fibration^.lift h)^.obj_im
--     (P_Fibration^.lift h)^.hom
--     (P_Fibration^.lift h)^.hom_im
--     (cart^.char f g' ωchar)
--     (cart^.char_im _ _ _)
--     (cart^.comm _ _ _)

-- /-! #brief Fibrations can factorize.
-- -/
-- definition Fibration.zigzag_in {E : Cat.{ℓobj ℓhom}} {B : Cat.{ℓobjb ℓhomb}}
--     (P : Fun E B)
--     (P_Fibration : Fibration P)
--     {a c : ⟦E⟧} {f : ⟦E : a →→ c⟧} {b : ⟦B⟧} {h : ⟦B : b →→ P^.obj c⟧}
--     {g : ⟦B : P^.obj a →→ b⟧} {ω : P^.hom f = h ∘∘ g}
--     (fac : ConducheFact P f h g ω)
--     : E^.hom fac^.obj (Fibration.factorize P P_Fibration f h g ω)^.obj
-- := let cart := (P_Fibration^.lift h)^.hom_cart
-- in cart^.char fac^.left (cast_hom (eq.trans fac^.obj_im (eq.symm (P_Fibration^.lift h)^.obj_im)))
--     begin
--       rw (P_Fibration^.lift h)^.hom_im,
--       refine eq.trans _ (eq.symm fac^.left_im),
--       rw -B^.circ_assoc,
--       apply Cat.circ.congr_right,
--       rw cast_hom.circ
--     end

-- /-! #brief Fibrations can factorize.
-- -/
-- definition Fibration.zigzag_out {E : Cat.{ℓobj ℓhom}} {B : Cat.{ℓobjb ℓhomb}}
--     (P : Fun E B)
--     (P_Fibration : Fibration P)
--     {a c : ⟦E⟧} {f : ⟦E : a →→ c⟧} {b : ⟦B⟧} {h : ⟦B : b →→ P^.obj c⟧}
--     {g : ⟦B : P^.obj a →→ b⟧} {ω : P^.hom f = h ∘∘ g}
--     (fac : ConducheFact P f h g ω)
--     : E^.hom (Fibration.factorize P P_Fibration f h g ω)^.obj fac^.obj
-- := let f₂ : ⟦E : (P_Fibration^.lift (cast_hom (eq.symm (fac^.obj_im)) ∘∘ g))^.obj →→ fac^.obj⟧
--           := (P_Fibration^.lift (P^.hom fac^.right))^.hom ∘∘ cast_hom begin rw fac^.right_im end
-- in let baz := (P_Fibration^.lift (cast_hom (eq.symm (fac^.obj_im)) ∘∘ g))^.hom_cart
-- in let bar := @CartesianHom.char _ _ _ _ _ _ baz
-- in let moo := (P_Fibration^.lift (cast_hom (eq.symm (fac^.obj_im)) ∘∘ g))^.obj_im
-- --in let moo := @CartesianHom.char _ _ _ _ _ _ (P_Fibration^.lift h)^.hom_cart
-- in f₂ ∘∘
-- begin
-- dsimp [Fibration.factorize],
-- exact sorry
-- end


-- /-! #brief Fibrations can factorize.
-- -/
-- definition Fibration.zigzag {E : Cat.{ℓobj ℓhom}} {B : Cat.{ℓobjb ℓhomb}}
--     (P : Fun E B)
--     (P_Fibration : Fibration P)
--     {a c : ⟦E⟧} {f : ⟦E : a →→ c⟧} {b : ⟦B⟧} {h : ⟦B : b →→ P^.obj c⟧}
--     {g : ⟦B : P^.obj a →→ b⟧} {ω : P^.hom f = h ∘∘ g}
--     (fac₁ fac₂ : ConducheFact P f h g ω)
--     : E^.hom fac₁^.obj fac₂^.obj
-- := E^.circ (Fibration.zigzag_out P P_Fibration fac₂)
--            (Fibration.zigzag_in P P_Fibration fac₁)


-- /-! #brief Fibrations are Conduché.
-- -/
-- definition Fibration.Conduche {E : Cat.{ℓobj ℓhom}} {B : Cat.{ℓobjb ℓhomb}}
--     (P : Fun E B)
--     (P_Fibration : Fibration P)
--     : Conduche P
-- := { factorize := @Fibration.factorize E B P P_Fibration
--    , zigzag := @Fibration.zigzag E B P P_Fibration
--    , zigzag_im := begin end
--    , zigzag_left := begin end
--    , zigzag_right := begin end
--    }



end qp
