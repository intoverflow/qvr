/- -----------------------------------------------------------------------
Basic properties of LeanCat.
----------------------------------------------------------------------- -/

import ..c1_basic
import ..c2_limits
import ..c3_wtypes
import ..c4_topoi

namespace qp

open stdaux

universe variables ℓ' ℓ ℓobj ℓhom



/- -----------------------------------------------------------------------
Constant homs.
----------------------------------------------------------------------- -/

/-! #brief A constant hom in LeanCat.
-/
definition LeanCat.const_hom
    {X Y : LeanCat.{ℓ}^.obj}
    (y : Y)
    : LeanCat^.hom X Y
| x := y



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
Limits and colimits in over/under categories.
----------------------------------------------------------------------- -/


/-! #brief OverCat LeanCat has all co-limits.
-/
instance LeanCat.Over.HasAllCoLimits
    (B : LeanCat.{max ℓ ℓobj}^.obj)
    : HasAllCoLimits.{ℓobj ℓhom}
        (OverCat LeanCat.{max ℓ ℓobj} B)
:= { has_colimit
      := λ X L
         , HasCoLimit.show
            { obj := colimit (OverFun.out LeanCat B □□ L)
            , hom := sorry
            }
            (λ x, { hom := λ Lx, quot.mk _ { fst := x, snd := Lx }
                  , triangle := sorry
                  })
            (λ x₁ x₂ f, begin
                         apply OverHom.eq,
                         apply funext, intro Lx,
                         apply quot.sound,
                         apply exists.intro f,
                         trivial
                       end)
            sorry
            sorry
            sorry
   }



/- -----------------------------------------------------------------------
Products.
----------------------------------------------------------------------- -/


/-! #brief LeanCat has all products.
-/
instance LeanCat.HasAllProducts
    : HasAllProducts.{ℓ'} LeanCat.{max ℓ ℓ'}
:= { has_product
      := λ A factor
         , HasProduct.show LeanCat factor
            (∀ (a : A), factor a)
            (λ a fa, fa a)
            (λ T f t a, f a t)
            (λ T f a, rfl)
            (λ T f h ωh
             , begin
                 apply funext, intro t,
                 apply funext, intro a,
                 rw ωh,
                 trivial
               end)
   }

/-! #brief Finite product type in LeanCat.
-/
definition ListProd
    : ∀ (TT : list LeanCat.{ℓ}^.obj)
      , LeanCat.{ℓ}^.obj
| [] := punit
| [T] := T
| (T :: TT) := T × ListProd TT

/-! #brief Projection from finite product type in LeanCat.
-/
definition ListProd.π
    : ∀ (TT : list LeanCat.{ℓ}^.obj)
        (n : fin (list.length TT))
        (x : ListProd TT)
      , list.get TT n
| [] n x := fin.zero_elim n
| [T] (fin.mk 0 ω0) X := X
| [T] (fin.mk (nat.succ n) ωn) X := false.rec _ begin cases ωn, cases a end
| (T :: T₁ :: TT) (fin.mk 0 ω0) X := X^.fst
| (T :: T₁ :: TT) (fin.mk (nat.succ n) ωn) X := ListProd.π (T₁ :: TT) { val := n, is_lt := nat.lt_of_succ_lt_succ ωn } X^.snd

/-! #brief Enumerating a map into a finite product.
-/
definition ListProd.univ
    : ∀ (TT : list LeanCat.{ℓ}^.obj)
        (S : LeanCat.{ℓ}^.obj)
        (f : ∀ (n : ℕ)
               (ωn : n < list.length TT)
             , S → list.get TT { val := n, is_lt := ωn })
      , S → ListProd TT
| [] S f s := punit.star
| [T] S f s := f 0 (fin_of 0)^.is_lt s
| (T :: T₁ :: TT) S f s
:= ( f 0 (fin_of 0)^.is_lt s
   , ListProd.univ (T₁ :: TT) S (λ n ωn s', f (nat.succ n) (nat.succ_lt_succ ωn) s') s
   )

/-! #brief Factoring property of the universal map.
-/
definition ListProd.univ.factor
    : ∀ {TT : list LeanCat.{ℓ}^.obj}
        {S : LeanCat.{ℓ}^.obj}
        {f : ∀ (n : ℕ)
               (ωn : n < list.length TT)
             , S → list.get TT { val := n, is_lt := ωn }}
        {n : ℕ} {ωn : n < list.length TT}
        {s : S}
      , f n ωn s = ListProd.π TT
                    { val := n, is_lt := ωn }
                    (ListProd.univ TT S f s)
| [] S f n ωn s := by cases ωn
| [T] S f 0 ω0 s := rfl
| [T] S f (nat.succ n) ωn s := false.rec _ begin cases ωn, cases a end
| (T :: T₁ :: TT) S f 0 ω0 s := rfl
| (T :: T₁ :: TT) S f (nat.succ n) ωn s
:= begin
     refine eq.trans _ (@ListProd.univ.factor (T₁ :: TT) S _ n _ s),
     trivial
   end

/-! #brief LeanCat has all finite products.
-/
instance LeanCat.HasFinProduct (factor : list LeanCat.{ℓ}^.obj)
    : HasFinProduct LeanCat factor
:= HasProduct.show LeanCat (list.get factor)
    (ListProd factor)
    (ListProd.π factor)
    (λ T f, ListProd.univ factor T (λ n ωn, f { val := n, is_lt := ωn }))
    (λ T f n
      , begin
          apply funext, intro t,
          cases n with n ωn,
          refine eq.trans _ (ListProd.univ.factor),
          trivial
        end)
    (λ T f h ωh
      , begin
          assert ωf : f = λ n t, ListProd.π factor n (h t),
          { apply funext @ωh },
          subst ωf,
          apply funext, intro t,
          induction factor with T factor rec,
          { apply punit.uniq },
          cases factor with T₁ factor,
          { trivial },
          { apply prod.eq,
            { trivial },
            { refine eq.trans _ (rec (λ t, (h t)^.snd) _),
              { trivial },
              { intro n, trivial }
            }
          }
        end)

/-! #brief LeanCat has all finite products.
-/
instance LeanCat.HasAllFinProducts
    : HasAllFinProducts LeanCat.{ℓ}
:= { has_product := LeanCat.HasFinProduct
   }



/- -----------------------------------------------------------------------
Pullbacks.
----------------------------------------------------------------------- -/

/-! #brief LeanCat has all pullbacks.
-/
instance LeanCat.HasPullback
    {base : LeanCat.{ℓ}^.obj} {factor : list LeanCat.{ℓ}^.obj}
    {T : LeanCat.{ℓ}^.obj}
    (maps : @HomsIn LeanCat (base :: factor) T)
    : HasPullback LeanCat maps
:= HasPullback.show LeanCat.{ℓ} maps
    { p : finproduct LeanCat (base :: factor)
      // @HomsList.repeat LeanCat _ _
          (λ p', HomsIn.get maps (fin_of 0) (finproduct.π LeanCat (base :: factor) (fin_of 0) p))
          (list.length (base :: factor))
          = homs_in_comp_out maps (finproduct.cone LeanCat (base :: factor))^.Proj }
    (λ p, HomsIn.get maps (fin_of 0) (finproduct.π LeanCat (base :: factor) (fin_of 0) p^.val))
    (HomsOut.comp (finproduct.cone LeanCat (base :: factor))^.Proj (λ p, p^.val))
    begin
      cases maps with _ m_base _ maps,
      -- apply HomsList.eq,
      -- { trivial },
      -- induction maps with _ m₁ _ maps rec,
      -- { trivial },
      exact sorry
    end
    sorry
    sorry
    sorry


instance LeanCat.HasAllPullbacks
    : HasAllPullbacks LeanCat.{ℓ}
:= { has_pullback
      := λ base factor T maps
         , LeanCat.HasPullback maps
   }



/- -----------------------------------------------------------------------
Products in OverCat LeanCat.
----------------------------------------------------------------------- -/

/-! #brief OverCat LeanCat has finite products.
-/
instance LeanCat.Over.HasFinProduct
    (T₀ : LeanCat.{ℓ}^.obj)
    (factor : list (OverCat LeanCat T₀)^.obj)
    : HasFinProduct (OverCat LeanCat T₀) factor
:= OverCat.HasFinProduct LeanCat.{ℓ} T₀ factor



/- -----------------------------------------------------------------------
Exponentials.
----------------------------------------------------------------------- -/

/-! #brief LeanCat has exponential objects.
-/
instance LeanCat.HasExp₁ (T S₀ : LeanCat.{ℓ}^.obj) (S : list LeanCat.{ℓ}^.obj)
    : @HasExp LeanCat T (S₀ :: S)
:= { exp := λ LeanCat_HasAllFinProducts
            , finproduct LeanCat (S₀ :: S) → T
   , ev
      := λ LeanCat_HasAllFinProducts p
         , let factors := ((finproduct LeanCat (S₀ :: S) → T) :: S₀ :: S)
           in @finproduct.π LeanCat factors (@HasAllFinProducts.HasFinProduct _ LeanCat_HasAllFinProducts factors) (@fin_of (nat.succ _) 0) p
             (finproduct.iso _ (LeanCat.HasFinProduct factors) p)^.snd
   , univ
      := λ LeanCat_HasAllFinProducts A f a s
         , let a_s : finproduct LeanCat (A :: S₀ :: S)
                  := (a, s)
           in sorry -- f begin end
   , factor := λ LeanCat_HasAllFinProducts A e
               , begin
                   apply funext, intro p,
                   dsimp,
                   rw [LeanCat.simp_circ],
                   exact sorry
                 end
   , uniq := λ LeanCat_HasAllFinProducts ev' ωev'
             , begin
                 apply funext, intro p,
                 exact sorry
               end
   }



/- -----------------------------------------------------------------------
Exponentials in OverCat LeanCat.
----------------------------------------------------------------------- -/

-- /-! #brief LeanCat has exponential objects.
-- -/
-- definition LeanCat.Over.exp
--       (T₀ : LeanCat.{ℓ}^.obj)
--       (T S : (OverCat LeanCat T₀)^.obj)
--       : OverObj LeanCat.{ℓ} T₀
-- := { obj := Σ (t₀ : T₀)
--             , {s : S^.obj // S^.hom s = t₀}
--               → {t : T^.obj // T^.hom t = t₀}
--    , hom := λ t₀f, t₀f^.fst
--    }

-- /-! #brief LeanCat has exponential objects.
-- -/
-- instance LeanCat.Over.HasExp
--       (T₀ : LeanCat.{ℓ}^.obj)
--       (T S : (OverCat LeanCat T₀)^.obj)
--     : @HasExp (OverCat LeanCat T₀) T S
-- := { exp := LeanCat.Over.exp T₀ T S
--    , ev
--       := λ p_HasProd
--          , { hom := λ p, let f := (@finproduct.π (OverCat LeanCat T₀) [LeanCat.Over.exp T₀ T S, S] p_HasProd (@fin_of 1 0))^.hom p
--                       in let x := (@finproduct.π (OverCat LeanCat T₀) [LeanCat.Over.exp T₀ T S, S] p_HasProd (@fin_of 0 1))^.hom p
--                       in (f^.snd { val := x, property := sorry })^.val
--            , triangle := sorry
--            }
--    , univ
--       := λ A A_HasProd f
--          , { hom := λ a, ⟨ A^.hom a
--                          , λ s, { val := let foo := @finproduct.univ (OverCat LeanCat T₀) [A, S] A_HasProd A
--                                                       (OverHom.id LeanCat T₀ A
--                                                         ↗← { hom := LeanCat.const_hom s^.val
--                                                             , triangle := begin end
--                                                             }
--                                                         ↗←↗)
--                                          in f^.hom begin end -- (foo^.hom a)
--                                 , property := begin end
--                                 }
--                          ⟩
--            , triangle := begin end
--            }
--    , factor := λ A p_HasProd A_HasProd e
--                , begin
--                  end
--    , uniq := λ p_HasProd ev' ωev'
--              , begin
--                end
--    }



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
