/- -----------------------------------------------------------------------
Subobject classifiers.
----------------------------------------------------------------------- -/

import ..c2_limits

namespace qp

open stdaux

universe variables ℓ ℓobj ℓhom

/-! #brief A subobject classifier.
-/
class HasSubobjClass (C : Cat.{ℓobj ℓhom})
:= (prop : ∀ [C_HasFinal : HasFinal C], C^.obj)
   (true : ∀ [C_HasFinal : HasFinal C]
           , C^.hom (final C) prop)
   (char
     : ∀ [C_HasFinal : HasFinal C]
         {U X : C^.obj}
         {m : C^.hom U X}
         (m_Monic : Monic m)
       , C^.hom X prop)
   (char_pullback
     : ∀ [C_HasFinal : HasFinal C]
         {U X : C^.obj}
         {m : C^.hom U X}
         (m_Monic : Monic m)
       , IsPullback (char m_Monic) m true (final_hom U))
   (char_uniq
     : ∀ [C_HasFinal : HasFinal C]
         {U X : C^.obj}
         {m : C^.hom U X}
         (m_Monic : Monic m)
         (char' : C^.hom X prop)
         (ω : IsPullback char' m true (final_hom U))
       , char' = char m_Monic)

/-! #brief Helper for showing a category has a subobject classifier.
-/
definition HasSubobjClass.show {C : Cat.{ℓobj ℓhom}}
    (prop
      : ∀ [C_HasFinal : HasFinal C]
        , C^.obj)
    (true
      : ∀ [C_HasFinal : HasFinal C]
        , C^.hom (final C) prop)
    (char
      : ∀ [C_HasFinal : HasFinal C]
          {U X : C^.obj} {m : C^.hom U X}
          (m_Monic : Monic m)
        , C^.hom X prop)
    (univ
      : ∀ [C_HasFinal : HasFinal C]
          {U V X : C^.obj} {m : C^.hom U X}
          (m_Monic : Monic m)
          (h : C^.hom V X)
          (ωh : char m_Monic ∘∘ h = true∘∘final_hom V)
        , C^.hom V U)
    (ωchar_comm
      : ∀ [C_HasFinal : HasFinal C]
          {U X : C^.obj} {m : C^.hom U X}
          (m_Monic : Monic m)
        , char m_Monic ∘∘ m = true ∘∘ final_hom U)
    (ωuniv
      : ∀ [C_HasFinal : HasFinal C]
          {U V X : C^.obj} {m : C^.hom U X}
          (m_Monic : Monic m)
          (h : C^.hom V X)
          (ωh : char m_Monic ∘∘ h = true∘∘final_hom V)
        , h = m ∘∘ univ m_Monic h ωh)
    (ωuniv_uniq
      : ∀ [C_HasFinal : HasFinal C]
          {U V X : C^.obj} {m : C^.hom U X}
          (m_Monic : Monic m)
          (h : C^.hom V U)
          (ω : char m_Monic ∘∘ (m ∘∘ h) = true ∘∘ final_hom V)
        , h = univ m_Monic (m ∘∘ h) ω)
    (ωchar_uniq
      : ∀ [C_HasFinal : HasFinal C]
          {U X : C^.obj} {m : C^.hom U X}
          (m_Monic : Monic m)
          (char' : C^.hom X prop)
          (char'_IsPullback : IsPullback char' m true (final_hom U))
        , char' = char m_Monic)
    : HasSubobjClass C
:= { prop := @prop
   , true := @true
   , char := @char
   , char_pullback
      := λ C_HasFinal U X m m_Monic
         , { has_pullback
              := HasPullback.show C _ U
                  (C^.circ (@char C_HasFinal U X m m_Monic) m)
                  (m ↗← @final_hom _ C_HasFinal U ↗←↗)
                  begin
                    apply dlist.eq,
                    { trivial },
                    apply dlist.eq,
                    { apply ωchar_comm },
                    trivial
                  end
                  (λ V hom ωhom
                   , begin
                       cases hom with _ h _ hom,
                       cases hom with _ h₂ _ _,
                       cases bb,
                       assert ωh₂ : h₂ = final_hom V,
                       { apply final_hom.uniq },
                       subst ωh₂,
                       assert ωh : char m_Monic ∘∘ h = true ∘∘ final_hom V,
                       { apply HomsList.congr_get ωhom (@fin_of 0 1) },
                       exact univ m_Monic h ωh
                     end)
                  (λ V hom ωhom
                   , begin
                       cases hom with _ h _ hom,
                       cases hom with _ h₂ _ _,
                       cases bb,
                       assert ωh₂ : h₂ = final_hom V,
                       { apply final_hom.uniq },
                       subst ωh₂,
                       apply dlist.eq,
                       { apply ωuniv },
                       apply dlist.eq,
                       { apply eq.symm (final_hom.uniq _) },
                       trivial
                     end)
                  (λ V hom ωhom h ωh
                   , begin
                       cases hom with _ h₁ _ hom,
                       cases hom with _ h₂ _ _,
                       cases bb,
                       assert ωh₂ : h₂ = final_hom V,
                       { apply final_hom.uniq },
                       subst ωh₂,
                       assert ωh₁ : h₁ = m ∘∘ h,
                       { apply dlist.congr_get ωh (@fin_of 1 0) },
                       subst ωh₁,
                       apply ωuniv_uniq
                     end)
           , ωpullback := rfl
           , ωπ₁ := eq.symm C^.circ_id_right
           , ωπ₂ := eq.symm C^.circ_id_right
           }
   , char_uniq := @ωchar_uniq
   }


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
