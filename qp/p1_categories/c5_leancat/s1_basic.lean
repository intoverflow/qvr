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


/-! #brief Structure hom for colimits in OverCat LeanCat.
-/
definition LeanCat.Over.HasCoLimit.colim_hom
    (B : LeanCat.{max ℓ ℓobj}^.obj)
    {X : Cat.{ℓobj ℓhom}}
    (L : Fun X (OverCat LeanCat B))
    : LeanCat^.hom (colimit (OverFun.out LeanCat B □□ L)) B
:= let f : (Σ (x : X^.obj), (L^.obj x)^.obj) → B
        := λ x, (L^.obj x^.fst)^.hom x^.snd
in quot.lift f
    begin
      intros a b,
      cases a with xa a,
      cases b with xb b,
      intro ω, cases ω with h ωb,
      dsimp at h,
      dsimp at ωb, subst ωb,
      apply congr_fun (L^.hom h)^.triangle a
    end

/-! #brief OverCat LeanCat has all co-limits.
-/
instance LeanCat.Over.HasCoLimit
    (B : LeanCat.{max ℓ ℓobj}^.obj)
    {X : Cat.{ℓobj ℓhom}} (L : Fun X (OverCat LeanCat B))
    : HasCoLimit L
:= HasCoLimit.show
    { obj := colimit (OverFun.out LeanCat B □□ L)
    , hom := LeanCat.Over.HasCoLimit.colim_hom B L
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

instance LeanCat.Over.HasAllCoLimits
    (B : LeanCat.{max ℓ ℓobj}^.obj)
    : HasAllCoLimits.{ℓobj ℓhom}
        (OverCat LeanCat.{max ℓ ℓobj} B)
:= { has_colimit := @LeanCat.Over.HasCoLimit B
   }      

/-! #brief Handy simplifier.
-/
theorem LeanCat.Over.HasCoLimit.obj
    (B : LeanCat.{max ℓ ℓobj}^.obj)
    {X : Cat.{ℓobj ℓhom}} (L : Fun X (OverCat LeanCat B))
    : (colimit L)^.obj = colimit (OverFun.out LeanCat B □□ L)
:= rfl



/- -----------------------------------------------------------------------
Products.
----------------------------------------------------------------------- -/

/-! #brief LeanCat has all products.
-/
instance LeanCat.HasProduct
    {A : Type ℓ'} (factor : A → LeanCat.{max ℓ ℓ'}^.obj)
    : HasProduct LeanCat.{max ℓ ℓ'} factor
:= HasProduct.show LeanCat factor
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

/-! #brief LeanCat has all products.
-/
instance LeanCat.HasAllProducts
    : HasAllProducts.{ℓ'} LeanCat.{max ℓ ℓ'}
:= { has_product := @LeanCat.HasProduct
   }

/-! #brief Finite product type in LeanCat.
-/
definition ListProd
    : ∀ (TT : list LeanCat.{ℓ}^.obj)
      , LeanCat.{ℓ}^.obj
| [] := punit
| [T] := T
| (T :: TT) := T × ListProd TT

/-! #brief A fancy way of mapping through a ListProd.
-/
definition {ℓb ℓx ℓy} ListProd.map
    {Ba : Type ℓb} {Tx : Ba → Type ℓx} {Ty : Ba → Type ℓy}
    (f : ∀ (b : Ba), Tx b → Ty b)
    : ∀ (BB : list Ba)
      , ListProd (list.map Tx BB)
      → ListProd (list.map Ty BB)
| [] _ := punit.star
| [Ba] x := f Ba x
| (Ba :: Ba₀ :: BB) (prod.mk x xx) := (f Ba x, @ListProd.map (Ba₀ :: BB) xx)

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
Co-products.
----------------------------------------------------------------------- -/

/-! #brief LeanCat has all co-products.
-/
instance LeanCat.HasCoProduct
    {A : Type ℓ'} (factor : A → LeanCat.{max ℓ ℓ'}^.obj)
    : HasCoProduct LeanCat.{max ℓ ℓ'} factor
:= HasCoProduct.show LeanCat factor
    (Σ (a : A), factor a)
    (sigma.mk)
    (λ T f af, f af^.fst af^.snd)
    (λ T f a, rfl)
    (λ T f h ωh
      , begin
          apply funext, intro af,
          cases af with a f,
          rw ωh,
          trivial
        end)

/-! #brief LeanCat has all co-products.
-/
instance LeanCat.HasAllCoProducts
    : HasAllCoProducts.{ℓ'} LeanCat.{max ℓ ℓ'}
:= { has_coproduct := @LeanCat.HasCoProduct
   }

/-! #brief Finite sum type in LeanCat.
-/
definition ListSum
    : ∀ (TT : list LeanCat.{ℓ}^.obj)
      , LeanCat.{ℓ}^.obj
| [] := pempty
| [T] := T
| (T :: TT) := sum T (ListSum TT)

/-! #brief A fancy way of mapping through a ListSum.
-/
definition {ℓb ℓx ℓy} ListSum.map
    {Ba : Type ℓb} {Tx : Ba → Type ℓx} {Ty : Ba → Type ℓy}
    : ∀ (BB : list Ba)
        (f : ∀ (n : ℕ) (ωn : n < list.length BB)
             , Tx (list.get BB {val := n, is_lt := ωn}) → Ty (list.get BB {val := n, is_lt := ωn}))
      , ListSum (list.map Tx BB)
      → ListSum (list.map Ty BB)
| [] f e := by cases e
| [Ba] f x := f 0 fin.zero^.is_lt x
| (Ba :: Ba₀ :: BB) f (sum.inl x) := sum.inl (f 0 fin.zero^.is_lt x)
| (Ba :: Ba₀ :: BB) f (sum.inr xx)
:= sum.inr (ListSum.map (Ba₀ :: BB)
             (λ n ωn, f (nat.succ n) (nat.succ_le_succ ωn))
            xx)

/-! #brief Inclusion into finite sum type in LeanCat.
-/
definition ListSum.ι
    : ∀ (TT : list LeanCat.{ℓ}^.obj)
        (n : fin (list.length TT))
        (x : list.get TT n)
      , ListSum TT
| [] n x := fin.zero_elim n
| [T] (fin.mk 0 ω0) x := x
| [T] (fin.mk (nat.succ n) ωn) x := false.rec _ begin cases ωn, cases a end
| (T :: T₁ :: TT) (fin.mk 0 ω0) x := sum.inl x
| (T :: T₁ :: TT) (fin.mk (nat.succ n) ωn) x
:= sum.inr (ListSum.ι (T₁ :: TT) { val := n, is_lt := nat.lt_of_succ_lt_succ ωn } x)

/-! #brief Enumerating a map out of a finite sum.
-/
definition ListSum.univ
    : ∀ (TT : list LeanCat.{ℓ}^.obj)
        (S : LeanCat.{ℓ}^.obj)
        (f : ∀ (n : ℕ)
               (ωn : n < list.length TT)
             , list.get TT { val := n, is_lt := ωn } → S)
      , ListSum TT → S
| [] S f e := by cases e
| [T] S f s := f 0 (fin_of 0)^.is_lt s
| (T :: T₁ :: TT) S f (sum.inl s)
:= f 0 (fin_of 0)^.is_lt s
| (T :: T₁ :: TT) S f (sum.inr s)
:= ListSum.univ (T₁ :: TT) S (λ n ωn s', f (nat.succ n) (nat.succ_lt_succ ωn) s') s

/-! #brief Factoring property of the universal map.
-/
definition ListSum.univ.factor
    : ∀ {TT : list LeanCat.{ℓ}^.obj}
        {S : LeanCat.{ℓ}^.obj}
        {f : ∀ (n : ℕ)
               (ωn : n < list.length TT)
             , list.get TT { val := n, is_lt := ωn } → S}
        {n : ℕ} {ωn : n < list.length TT}
        {s : list.get TT { val := n, is_lt := ωn }}
      , f n ωn s = ListSum.univ TT S f
                     (ListSum.ι TT { val := n, is_lt := ωn } s)
| [] S f n ωn s := by cases ωn
| [T] S f 0 ω0 s := rfl
| [T] S f (nat.succ n) ωn s := false.rec _ begin cases ωn, cases a end
| (T :: T₁ :: TT) S f 0 ω0 s := rfl
| (T :: T₁ :: TT) S f (nat.succ n) ωn s
:= begin
     refine eq.trans _ (@ListSum.univ.factor (T₁ :: TT) S _ n _ s),
     trivial
   end

/-! #brief LeanCat has all finite products.
-/
instance LeanCat.HasFinCoProduct (factor : list LeanCat.{ℓ}^.obj)
    : HasFinCoProduct LeanCat factor
:= HasCoProduct.show LeanCat (list.get factor)
    (ListSum factor)
    (ListSum.ι factor)
    (λ T f, ListSum.univ factor T (λ n ωn, f { val := n, is_lt := ωn }))
    (λ T f n
      , begin
          apply funext, intro t,
          cases n with n ωn,
          refine eq.trans _ (ListSum.univ.factor),
          trivial
        end)
    (λ T f h ωh
      , begin
          assert ωf : f = λ n t, h (ListSum.ι factor n t),
          { apply funext @ωh },
          subst ωf,
          apply funext, intro t,
          induction factor with T factor rec,
          { cases t },
          cases factor with T₁ factor,
          { trivial },
          { cases t,
            { trivial },
            { refine eq.trans _ (rec (λ a, (h (sum.inr a))) _ _),
              { trivial },
              { intro n, trivial }
            }
          }
        end)

/-! #brief LeanCat has all finite products.
-/
instance LeanCat.HasAllFinCoProducts
    : HasAllFinCoProducts LeanCat.{ℓ}
:= { has_coproduct := LeanCat.HasFinCoProduct
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
      // ∀ (n : fin (list.length (base :: factor)))
         , HomsIn.get maps (fin_of 0) (finproduct.π LeanCat (base :: factor) (fin_of 0) p)
            = HomsIn.get maps n (finproduct.π LeanCat (base :: factor) n p)
    }
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

/-! #brief A handy wrapper.
-/
definition LeanCat.BaseChangeFun
    {X Y : LeanCat.{ℓ}^.obj}
    (f : LeanCat.{ℓ}^.hom X Y)
    : Fun (OverCat LeanCat Y) (OverCat LeanCat X)
:= @BaseChangeFun LeanCat X Y f
     (HasAllPullbacks.HasPullbacksAlong LeanCat f)



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
instance LeanCat.HasExp (X Y : LeanCat.{ℓ}^.obj)
    : @HasExp LeanCat X Y
:= { exp := Y → X
   , ev
      := λ exp_Y_HasFinProduct p
         , let f := @finproduct.π _ _ exp_Y_HasFinProduct (@fin_of 1 0)
        in let y := @finproduct.π _ _ exp_Y_HasFinProduct (@fin_of 0 1)
        in f p (y p)
   , univ
      := λ Z Z_Y_HasFinProduct e z y
         , e (finproduct.iso (LeanCat.HasFinProduct [Z, Y]) Z_Y_HasFinProduct (z, y))
   , factor := λ exp_Y_HasFinProduct Z Z_Y_HasFinProduct e
               , begin
                   apply funext, intro zy,
                   rw LeanCat.simp_circ,
                   dsimp,
                   exact sorry
                 end
   , uniq := λ exp_Y_HasFinProduct Z Z_Y_HasFinProduct e u ωu
             , begin
                 apply funext, intro z,
                 apply funext, intro y,
                 rw ωu,
                 exact sorry
               end
   }



/- -----------------------------------------------------------------------
Exponentials in OverCat LeanCat.
----------------------------------------------------------------------- -/

/-! #brief LeanCat has exponential objects.
-/
definition LeanCat.Over.exp
      (T₀ : LeanCat.{ℓ}^.obj)
      (T S : (OverCat LeanCat T₀)^.obj)
      : OverObj LeanCat.{ℓ} T₀
:= { obj := Σ (t₀ : T₀)
            , {s : S^.dom // S^.hom s = t₀}
              → {t : T^.obj // T^.hom t = t₀}
   , hom := sigma.fst
   }

/-! #brief LeanCat has exponential objects.
-/
instance LeanCat.Over.HasExp
      (T₀ : LeanCat.{ℓ}^.obj)
      (X Y : (OverCat LeanCat T₀)^.obj)
    : @HasExp (OverCat LeanCat T₀) X Y
:= { exp := LeanCat.Over.exp T₀ X Y
   , ev
      := λ p_HasProd
         , { hom := λ p, let f := (@finproduct.π (OverCat LeanCat T₀) [LeanCat.Over.exp T₀ X Y, Y] p_HasProd (@fin_of 1 0))^.hom p
                      in let y := (@finproduct.π (OverCat LeanCat T₀) [LeanCat.Over.exp T₀ X Y, Y] p_HasProd (@fin_of 0 1))^.hom p
                      in (f^.snd { val := y, property := sorry })^.val
           , triangle := sorry
           }
   , univ
      := λ A A_HasProd f
         , let a_y : ∀ (a : A^.obj)
                       (y : {s // Y^.hom s = A^.hom a})
                     , OverObj.dom (finproduct (OverCat LeanCat T₀) [A, Y])
                   := λ a y
                      , { val := (a, y^.val)
                        , property
                           := begin
                                intro nωn, cases nωn with n ωn,
                                cases n with n, { trivial },
                                cases n with n, { apply eq.symm y^.property },
                                apply nat.not_lt_add_right n 2 ωn
                              end
                        }
        in let a_y' := λ a y, ((finproduct.iso (LeanCat.Over.HasFinProduct T₀ [A, Y]) A_HasProd)^.hom (a_y a y))
        in { hom
              := λ a
                 , ⟨ A^.hom a
                   , λ y, { val := f^.hom (a_y' a y)
                          , property := begin
                                          refine eq.trans (congr_fun (eq.symm f^.triangle) (a_y' a y)) _,
                                          exact sorry
                                        end
                          }
                   ⟩
         , triangle := sorry
         }
   , factor := λ A p_HasProd A_HasProd e
               , sorry
   , uniq := λ exp_Y_HasFinProduct Z Z_Y_HasFinProduct e u ωu
             , sorry
   }

/-! #brief OverCat LeanCat has all exponentials.
-/
instance LeanCat.Over.HasAllExp
    (T₀ : LeanCat.{ℓ}^.obj)
    : @HasAllExp (OverCat LeanCat T₀)
:= { has_exp := LeanCat.Over.HasExp T₀
   }

/-! #brief LeanCat has exponentials in all slices.
-/
instance LeanCat.HasAllLocalExp
    : HasAllLocalExp LeanCat.{ℓ}
:= { has_exp := LeanCat.Over.HasExp
   }


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



/- -----------------------------------------------------------------------
Natural numbers object.
----------------------------------------------------------------------- -/

/-! #brief LeanCat has an NNO.
-/
instance LeanCat.HasNNO
    : @HasNNO LeanCat.{ℓ} LeanCat.HasFinal
:= { nn := Lean.LevelMax ℕ
   , zero := λ u, Lean.LevelMax.lift 0
   , succ := Lean.LevelMax.map nat.succ
   , univ := λ A z s n, nat.rec_on (Lean.LevelMax.unlift n)
                         (z punit.star)
                         (λ n' a, s a)
   , comm_zero
      := λ A z s
         , begin
             apply funext, intro u, cases u,
             trivial
           end
   , comm_succ
      := λ A z s
         , begin
             apply funext, intro n, cases n with n,
             induction n with n rec,
             { trivial },
             { apply congr_arg s,
               apply rec
             }
           end
   , uniq
      := λ A z s u' ωzero ωsucc
         , begin
             apply funext, intro n, cases n with n,
             induction n with n rec,
             { rw ωzero, trivial },
             { refine eq.trans (eq.symm (congr_fun ωsucc (Lean.LevelMax.lift n))) _,
               apply congr_arg s rec
             }
           end
   }

end qp
