/- -----------------------------------------------------------------------
Basic properties of LeanCat.
----------------------------------------------------------------------- -/

import ..c1_basic
import ..c2_limits
import ..c3_wtypes
import ..c4_topoi

namespace qp

open stdaux

universe variables ℓ ℓobj ℓhom


/- -----------------------------------------------------------------------
Limits and colimits.
----------------------------------------------------------------------- -/

/-! #brief LeanCat has all limits.
-/
instance LeanCat.HasAllLimits : HasAllLimits.{ℓobj ℓhom} LeanCat.{max ℓ ℓobj}
:= { has_limit
      := λ X L
         , HasLimit.show
            { g : ∀ (x : X^.obj), L^.obj x
               // ∀ {x₁ x₂ : X^.obj} (f : X^.hom x₁ x₂)
                  , g x₂ = L^.hom f (g x₁)
            }
            (λ x g, g^.val x)
            (λ x₁ x₂ f, funext (λ g, g^.property f))
            (λ C hom ωhom c
             , { val := λ x, hom x c
               , property := λ x₁ x₂ f, begin rw ωhom f, trivial end
               })
            (λ C hom ωhom x, rfl)
            (λ C hom ωhom f ωf
             , funext (λ c, subtype.eq (funext (λ x, eq.symm (by apply congr_fun (ωf x) c)))))
   }

/-! #brief The equivalence relation underlying colimits in LeanCat.
-/
definition LeanCat.HasAllCoLimits.prop {X : Cat.{ℓobj ℓhom}}
    (L : Fun X LeanCat.{max ℓ ℓobj})
    (a b : (Σ (x : X^.obj), L^.obj x))
    : Prop
:= ∃ (f : X^.hom a^.fst b^.fst), b^.snd = L^.hom f a^.snd

/-! #brief LeanCat has all co-limits.
-/
instance LeanCat.HasAllCoLimits : HasAllCoLimits.{ℓobj ℓhom} LeanCat.{max ℓ ℓobj}
:= { has_colimit
      := λ X L
         , HasCoLimit.show
            (quot (LeanCat.HasAllCoLimits.prop L))
            (λ x Lx, quot.mk _ {fst := x, snd := Lx})
            (λ x₁ x₂ f, funext (λ Lx, quot.sound (exists.intro f rfl)))
            (λ C hom ωhom
             , let f : (Σ (x : X^.obj), L^.obj x) → C
                      := λ Lx, hom Lx^.fst Lx^.snd in
               let ωf : ∀ (a b : Σ (x : ⟦X⟧), L^.obj x)
                        , LeanCat.HasAllCoLimits.prop L a b
                        → f a = f b
                     := λ a b ωab
                        , begin
                            dsimp,
                            cases ωab with g ωg,
                            rw [ωg, ωhom g],
                            trivial
                          end
               in quot.lift f ωf)
            (λ C hom ωhom x, rfl)
            (λ C hom ωhom f ωf
             , funext (quot.ind (begin
                                   intro Lx,
                                   cases Lx with x Lx,
                                   apply eq.symm (congr_fun (ωf x) Lx)
                                 end)))
   }



/- -----------------------------------------------------------------------
Products.
----------------------------------------------------------------------- -/



/- -----------------------------------------------------------------------
Pullbacks.
----------------------------------------------------------------------- -/




/- -----------------------------------------------------------------------
Subobject classifiers.
----------------------------------------------------------------------- -/

/-! #brief Axiom of choice gives LeanCat a subobject classifier.
-/
noncomputable instance LeanCat.HasSubobjClass
    : HasSubobjClass LeanCat.{ℓ}
:= HasSubobjClass.show
    (λ LeanCat_HasFinal, Lean.LevelMax Prop)
    (λ LeanCat_HasFinal, λ u, Lean.LevelMax.lift true)
    (λ LeanCat_HasFinal U X m m_Monic, λ x, Lean.LevelMax.lift (∃ (u : U), m u = x))
    (λ LeanCat_HasFinal U X V m m_Monic h ωh x
     , let u₀ : ∃ (u : U), m u = h x
             := begin
                  apply of_iff_true,
                  apply eq.to_iff,
                  apply Lean.LevelMax.lift.inj,
                  apply congr_fun ωh
                end in
       let u : ∃! (u : U), h x = m u
            := exists.elim u₀
                (λ u ωu
                 , exists_unique.intro u (eq.symm ωu)
                    (λ u' ωu', LeanCat.Monic.inj m_Monic
                                (eq.symm (eq.trans ωu ωu'))))
       in unique_choice u)
    (λ LeanCat_HasFinal U X m m_Monic
     , begin
         apply funext, intro u,
         apply congr_arg Lean.LevelMax.lift,
         apply iff.to_eq,
         apply iff_true_intro,
         apply exists.intro u,
         trivial
       end)
    (λ LeanCat_HasFinal U V X m m_Monic h ωh
     , begin
         apply funext, intro v,
         dsimp, unfold LeanCat SortCat, dsimp,
         generalize (of_iff_true (eq.to_iff (Lean.LevelMax.lift.inj (congr_fun ωh v)))) ω,
         intro ω, cases ω with u ωu,
         refine eq.trans (eq.symm _) (eq.symm (congr_arg m unique_choice.simp)),
         exact ωu
       end)
    (λ LeanCat_HasFinal U V X m m_Monic h ωh
     , begin
         apply funext, intro v,
         generalize (of_iff_true (eq.to_iff (Lean.LevelMax.lift.inj (congr_fun ωh v)))) ω,
         intro ω, cases ω with u ωu,
         refine eq.trans _ (eq.symm unique_choice.simp),
         apply LeanCat.Monic.inj m_Monic,
         exact eq.symm ωu
       end)
    (λ LeanCat_HasFinal U X m m_Monic char' char'_IsPullback
     , sorry)


--    , char_uniq
--       := λ LeanCat_HasFinal U X m m_Monic char' ωchar'
--          , let char'' : X → Prop
--                      := λ x, Lean.LevelMax.cases_on (char' x) (λ P, P)
--         in begin
--              apply funext, intro x,
--              assert ωchar'' : char' x = Lean.LevelMax.lift (Lean.LevelMax.cases_on (char' x) (λ P, P)),
--              { generalize (char' x) char'_x,
--                intro char'_x, cases char'_x,
--                trivial,
--              },
--              refine eq.trans ωchar'' (congr_arg Lean.LevelMax.lift _),
--              apply iff.to_eq,
--              apply iff.intro,
--              { intro ωP_x, exact sorry
--              },
--              { intro ωu, cases ωu with u ωu,
--                subst ωu,
--                -- true because ωchar' implies char' (m u) = Lean.LevelMax.lift true.
--                exact sorry
--              }
--            end
--    }


end qp
