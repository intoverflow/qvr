/- -----------------------------------------------------------------------
Subobject classifiers.
----------------------------------------------------------------------- -/

import ..c2_limits

namespace qp

open stdaux

universe variables ℓ ℓobj ℓhom ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂

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
         , IsPullback.show
            (λ V h₁ h₂ ωsquare
             , @univ C_HasFinal U V X m m_Monic h₁
                 begin
                   assert ωh₂ : h₂ = final_hom V,
                   { apply final_hom.uniq },
                   subst ωh₂,
                   exact ωsquare
                 end)
            (@ωchar_comm C_HasFinal U X m m_Monic)
            (λ V h₁ h₂ ωsquare
             , @ωuniv C_HasFinal U V X m m_Monic h₁
                 begin
                   assert ωh₂ : h₂ = final_hom V,
                   { apply final_hom.uniq },
                   subst ωh₂,
                   exact ωsquare
                 end)
            (λ V h₁ h₂ ωsquare
             , eq.trans (final_hom.uniq C) (eq.symm (final_hom.uniq C)))
            (λ V h₁ h₂ ωsquare h ωh₁ ωh₂
             , begin
                 subst ωh₁,
                 apply ωuniv_uniq
               end)
   , char_uniq := @ωchar_uniq
   }



/-! #brief Functor categories have pointwise subobject classifiers.
-/
definition FunCat.HasSubobjClass.char {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    [D_HasFinal : HasFinal D]
    [D_HasSubobjClass : HasSubobjClass D]
    {U F : Fun C D}
    {η : NatTrans U F}
    (η_Monic : @Monic (FunCat C D) U F η)
    : NatTrans F (ConstFun C (HasSubobjClass.prop D))
:= { com := λ c, HasSubobjClass.char (NatTrans.com.Monic η_Monic c)
   , natural
      := λ x y f
         , sorry
   }

/-! #brief Functor categories have pointwise subobject classifiers.
-/
definition FunCat.HasSubobjClass.univ {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    [D_HasFinal : HasFinal D]
    [D_HasSubobjClass : HasSubobjClass D]
    (FunCat_HasFinal : HasFinal (FunCat C D))
    {U F G : Fun C D}
    {ηUG : NatTrans U G}
    (ηUG_Monic : @Monic (FunCat C D) U G ηUG)
    (ηFG : NatTrans F G)
    (ωη : FunCat.HasSubobjClass.char ηUG_Monic ◇◇ ηFG
           = ConstTrans C (HasSubobjClass.true D)
              ◇◇ final.iso FunCat_HasFinal FunCat.HasFinal
              ◇◇ @final_hom (FunCat C D) FunCat_HasFinal F)
    : NatTrans F U
:= { com := λ c, ispullback.univ
                     (HasSubobjClass.char_pullback (NatTrans.com.Monic ηUG_Monic c))
                     (ηFG^.com c)
                     (final_hom (F^.obj c))
                     (begin
                        refine eq.trans (NatTrans.congr_com ωη) _,
                        dsimp [NatTrans.comp, ConstTrans],
                        rw -D^.circ_assoc,
                        apply Cat.circ.congr_right,
                        apply final_hom.uniq
                      end)
   , natural
      := λ x y f
         , sorry
   }

/-! #brief Functor categories have pointwise subobject classifiers.
-/
instance FunCat.HasSubobjClass {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    [D_HasFinal : HasFinal D]
    [D_HasSubobjClass : HasSubobjClass D]
    : HasSubobjClass (FunCat C D)
:= HasSubobjClass.show
    (λ FunCat_HasFinal, ConstFun C (HasSubobjClass.prop D))
    (λ FunCat_HasFinal
     , (FunCat C D)^.circ
        (ConstTrans C (HasSubobjClass.true D))
        (final.iso FunCat_HasFinal FunCat.HasFinal))
    (λ FunCat_HasFinal U F η η_Monic
     , FunCat.HasSubobjClass.char η_Monic)
    (λ FunCat_HasFinal U F G ηUG ηUG_Monic ηFG ω
     , FunCat.HasSubobjClass.univ FunCat_HasFinal ηUG_Monic ηFG ω)
    (λ FunCat_HasFinal U F η η_Monic
     , begin
         apply NatTrans.eq,
         apply funext, intro c,
         dsimp [FunCat, NatTrans.comp, FunCat.HasSubobjClass.char, ConstTrans],
         exact sorry
       end)
    (λ FunCat_HasFinal U F G η η_Monic h ωh
     , begin exact sorry end)
    (λ FunCat_HasFinal U X V m m_Monic h ωh
     , begin exact sorry end)
    (λ FunCat_HasFinal U X m m_Monic char' char'_IsPullback
     , begin exact sorry end)

end qp
