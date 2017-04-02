/- -----------------------------------------------------------------------
Pullbacks and pushouts.
----------------------------------------------------------------------- -/

import .s1_limits
import .s2_products

namespace qp

open stdaux

universe variables ℓobj ℓhom



/- -----------------------------------------------------------------------
Pullbacks.
----------------------------------------------------------------------- -/

/-! #brief Homs in a cospan category.
-/
inductive CoSpanHom (N : ℕ) : option (fin N) → option (fin N) → Type
| id : ∀ (x : option (fin N)), CoSpanHom x x
| hom : ∀ (n : fin N), CoSpanHom (some n) none

/-! #brief A cospan category.
-/
definition CoSpanCat (N : ℕ) : Cat.{0 1}
:= { obj := option (fin N)
   , hom := CoSpanHom N
   , id := CoSpanHom.id
   , circ := λ x y z g f, begin cases f, { exact g }, { cases g, apply CoSpanHom.hom } end
   , circ_assoc := λ x y z w h g f, begin cases f, { trivial }, { cases g, trivial } end
   , circ_id_left := λ x y f, begin cases f, { trivial }, { trivial } end
   , circ_id_right := λ x y f, begin cases f, { trivial }, { trivial } end
   }

/-! #brief A cospan diagram.
-/
definition PullbackDrgm (C : Cat.{ℓobj ℓhom})
    {base : C^.obj} {factor : list C^.obj} {t : C^.obj}
    (maps : HomsIn (base :: factor) t)
    : Fun (CoSpanCat (list.length (base :: factor))) C
:= { obj := λ a, option.cases_on a t (list.get (base :: factor))
   , hom := λ a₁ a₂ f, begin cases f, { apply C^.id }, { exact HomsIn.get maps n } end
   , hom_id := λ a, rfl
   , hom_circ := λ a₁ a₂ a₃ g f
                 , begin
                     cases f,
                     { apply eq.symm C^.circ_id_right },
                     { cases g, apply eq.symm C^.circ_id_left }
                   end
   }

/-! #brief A cone over a pullback.
-/
definition PullbackCone (C : Cat.{ℓobj ℓhom})
    {base : C^.obj} {factor : list C^.obj} {t : C^.obj}
    (maps : HomsIn (base :: factor) t)
    : Type (max ℓobj ℓhom)
:= Cone (PullbackDrgm C maps)

/-! #brief Helper for making a pullback cone.
-/
definition PullbackCone.mk {C : Cat.{ℓobj ℓhom}}
    {base : C^.obj} {factor : list C^.obj} {t : C^.obj}
    (maps : HomsIn (base :: factor) t)
    (c : C^.obj)
    (to_t : C^.hom c t)
    (proj : HomsOut c (base :: factor))
    (ωproj : HomsList.repeat to_t (list.length (base :: factor))
              = homs_in_comp_out maps proj)
    : PullbackCone C maps
:= { obj := c
   , hom := λ x, option.cases_on x to_t (HomsOut.get proj)
   , comm := λ x₁ x₂ f, begin
                         cases f,
                         { exact eq.symm C^.circ_id_left },
                         { unfold PullbackDrgm,
                           apply eq_of_heq,
                           refine heq.trans (heq.symm (HomsList.get_repeat to_t n)) _,
                           refine heq.trans _ (get_homs_in_comp_out maps proj),
                           rw ωproj
                         }
                       end
   }

/-! #brief The projections out of a pullback cone.
-/
definition PullbackCone.Proj {C : Cat.{ℓobj ℓhom}}
    {base : C^.obj} {factor : list C^.obj} {t : C^.obj}
    {maps : HomsIn (base :: factor) t}
    (cone : PullbackCone C maps)
    : HomsOut cone^.obj (base :: factor)
:= sorry -- HomsOut.enum (Cone.hom cone)

/-! #brief A pullback in a category.
-/
@[class] definition HasPullback (C : Cat.{ℓobj ℓhom})
    {base : C^.obj} {factor : list C^.obj} {t : C^.obj}
    (maps : HomsIn (base :: factor) t)
:= HasLimit (PullbackDrgm C maps)

instance HasPullback.HasLimit {C : Cat.{ℓobj ℓhom}}
    {base : C^.obj} {factor : list C^.obj} {t : C^.obj}
    (maps : HomsIn (base :: factor) t)
    [maps_HasPullback : HasPullback C maps]
    : HasLimit (PullbackDrgm C maps)
:= maps_HasPullback

/-! #brief A category with all pullbacks.
-/
class HasAllPullbacks (C : Cat.{ℓobj ℓhom})
:= (has_pullback : ∀ {base : C^.obj} {factor : list C^.obj} {t : C^.obj}
                     (maps : HomsIn (base :: factor) t)
                   , HasPullback C maps)

instance HasAllPullbacks.HasPullback (C : Cat.{ℓobj ℓhom})
    [C_HasAllPullbacks : HasAllPullbacks C]
    {base : C^.obj} {factor : list C^.obj} {t : C^.obj}
    (maps : HomsIn (base :: factor) t)
    : HasPullback C maps
:= HasAllPullbacks.has_pullback maps

/-! #brief A category with all pullbacks along a given hom.
-/
class HasPullbacksAlong (C : Cat.{ℓobj ℓhom})
    {base t : C^.obj} (f : C^.hom base t)
:= (has_pullback : ∀ {y : C^.obj} (map : C^.hom y t)
                   , HasPullback C (f ↗→ map ↗→↗))

instance HasPullbacksAlong.HasPullback (C : Cat.{ℓobj ℓhom})
    {base t : C^.obj} (f : C^.hom base t)
    {y : C^.obj} (map : C^.hom y t)
    [f_HasPullbacksAlong : HasPullbacksAlong C f]
    : HasPullback C (f ↗→ map ↗→↗)
:= HasPullbacksAlong.has_pullback f map

/-! #brief Helper for showing a category has a pullback.
-/
definition HasPullback.show (C : Cat.{ℓobj ℓhom})
    {base : C^.obj} {factor : list C^.obj} {t : C^.obj}
    (maps : HomsIn (base :: factor) t)
    (p : C^.obj)
    (to_t : C^.hom p t)
    (proj : HomsOut p (base :: factor))
    (ωproj : HomsList.repeat to_t (list.length (base :: factor))
              = homs_in_comp_out maps proj)
    (univ : ∀ (c : C^.obj) (hom : HomsOut c (base :: factor))
              (ωhom : HomsList.repeat
                       (C^.circ (HomsIn.get maps (fin_of 0))
                                (HomsOut.get hom (fin_of 0)))
                       (list.length (base :: factor))
                       = homs_in_comp_out maps hom)
            , C^.hom c p)
    (ωuniv : ∀ (c : C^.obj) (hom : HomsOut c (base :: factor))
              (ωhom : HomsList.repeat
                       (C^.circ (HomsIn.get maps (fin_of 0))
                                (HomsOut.get hom (fin_of 0)))
                       (list.length (base :: factor))
                       = homs_in_comp_out maps hom)
             , hom = HomsOut.comp proj (univ c hom ωhom))
    (ωuniq : ∀ (c : C^.obj) (hom : HomsOut c (base :: factor))
              (ωhom : HomsList.repeat
                       (C^.circ (HomsIn.get maps (fin_of 0))
                                (HomsOut.get hom (fin_of 0)))
                       (list.length (base :: factor))
                       = homs_in_comp_out maps hom)
               (h : C^.hom c p)
               (ωcomm : hom = HomsOut.comp proj h)
             , h = univ c hom ωhom)
    : HasPullback C maps
:= HasLimit.show p (λ x, option.cases_on x to_t ((HomsOut.get proj)))
    (λ x₁ x₂ f, begin
                 cases f,
                 { exact eq.symm C^.circ_id_left },
                 { unfold PullbackDrgm,
                   apply eq_of_heq,
                   refine heq.trans (heq.symm (HomsList.get_repeat to_t n)) _,
                   refine heq.trans _ (get_homs_in_comp_out maps proj),
                   rw ωproj
                 }
               end)
    (λ c hom ωcomm, univ c (HomsOut.enum (λ n, hom (some n)))
     begin
       exact sorry
     end)
    (λ c hom ωcomm a, begin exact sorry end)
    (λ c hom ωcomm h ωh, begin exact sorry end)

/-! #brief Pullbacks are cones.
-/
definition pullback.cone (C : Cat.{ℓobj ℓhom})
    {base : C^.obj} {factor : list C^.obj} {t : C^.obj}
    (maps : HomsIn (base :: factor) t)
    [maps_HasPullback : HasPullback C maps]
    : PullbackCone C maps
:= limit.cone (PullbackDrgm C maps)

/-! #brief The pullback of a collection of homs.
-/
definition pullback (C : Cat.{ℓobj ℓhom})
    {base : C^.obj} {factor : list C^.obj} {t : C^.obj}
    (maps : HomsIn (base :: factor) t)
    [maps_HasPullback : HasPullback C maps]
    : C^.obj
:= limit (PullbackDrgm C maps)

/-! #brief Projection out of a pullback.
-/
definition pullback.π (C : Cat.{ℓobj ℓhom})
    {base : C^.obj} {factor : list C^.obj} {t : C^.obj}
    (maps : HomsIn (base :: factor) t)
    [maps_HasPullback : HasPullback C maps]
    (n : fin (list.length (base :: factor)))
    : C^.hom (pullback C maps) (list.get (base :: factor) n)
:= limit.out (PullbackDrgm C maps) (some n)

/-! #brief Projection out of a pullback to the base.
-/
definition pullback.πbase (C : Cat.{ℓobj ℓhom})
    {base : C^.obj} {factor : list C^.obj} {t : C^.obj}
    (maps : HomsIn (base :: factor) t)
    [maps_HasPullback : HasPullback C maps]
    : C^.hom (pullback C maps) t
:= limit.out (PullbackDrgm C maps) none

/-! #brief Every cone is mediated through the pullback.
-/
definition pullback.univ (C : Cat.{ℓobj ℓhom})
    {base : C^.obj} {factor : list C^.obj} {t : C^.obj}
    (maps : HomsIn (base :: factor) t)
    [maps_HasPullback : HasPullback C maps]
    (c : PullbackCone C maps)
    : C^.hom c^.obj (pullback C maps)
:= limit.univ c

/-! #brief Every cone is mediated through the pullback.
-/
definition pullback.univ.mediates (C : Cat.{ℓobj ℓhom})
    {base : C^.obj} {factor : list C^.obj} {t : C^.obj}
    (maps : HomsIn (base :: factor) t)
    {maps_HasPullback : HasPullback C maps}
    (c : PullbackCone C maps)
    (n : fin (list.length (base :: factor)))
    : c^.hom (some n) = C^.circ (@pullback.π C base factor t maps maps_HasPullback n) (pullback.univ C maps c)
:= limit.univ.mediates c (some n)

/-! #brief Every cone is mediated through the pullback.
-/
definition pullback.univ.mediates_base (C : Cat.{ℓobj ℓhom})
    {base : C^.obj} {factor : list C^.obj} {t : C^.obj}
    (maps : HomsIn (base :: factor) t)
    {maps_HasPullback : HasPullback C maps}
    (c : PullbackCone C maps)
    : c^.hom none = C^.circ (@pullback.πbase C base factor t maps maps_HasPullback) (pullback.univ C maps c)
:= limit.univ.mediates c none

/-! #brief The mediating map from the cone to the pullback is unique.
-/
definition pullback.univ.uniq (C : Cat.{ℓobj ℓhom})
    {base : C^.obj} {factor : list C^.obj} {t : C^.obj}
    (maps : HomsIn (base :: factor) t)
    {maps_HasPullback : HasPullback C maps}
    (c : PullbackCone C maps)
    (m : C^.hom c^.obj (pullback C maps))
    (ω : ∀ (n : fin (list.length (base :: factor)))
         , c^.hom (some n) = (@pullback.π C base factor t maps maps_HasPullback n) ∘∘ m)
    (ωbase : c^.hom none = (@pullback.πbase C base factor t maps maps_HasPullback) ∘∘ m)
    : m = pullback.univ C maps c
:= limit.univ.uniq c m (λ x, option.cases_on x ωbase ω)

/-! #brief The unique iso between two pullbacks of the same homs.
-/
definition pullback.iso {C : Cat.{ℓobj ℓhom}}
    {base : C^.obj} {factor : list C^.obj} {t : C^.obj}
    {maps : HomsIn (base :: factor) t}
    (maps_HasPullback₁ maps_HasPullback₂ : HasPullback C maps)
    : C^.hom (@pullback C base factor t maps maps_HasPullback₁)
             (@pullback C base factor t maps maps_HasPullback₂)
:= limit.iso maps_HasPullback₁ maps_HasPullback₂

/-! #brief Pullbacks are unique up-to unique isomorphism.
-/
definition pullback.uniq {C : Cat.{ℓobj ℓhom}}
    {base : C^.obj} {factor : list C^.obj} {t : C^.obj}
    {maps : HomsIn (base :: factor) t}
    (maps_HasPullback₁ maps_HasPullback₂ : HasPullback C maps)
    : Iso (pullback.iso maps_HasPullback₁ maps_HasPullback₂)
          (pullback.iso maps_HasPullback₂ maps_HasPullback₁)
:= limit.uniq maps_HasPullback₁ maps_HasPullback₂

/-! #brief A pullback square.
-/
class IsPullback {C : Cat.{ℓobj ℓhom}}
    {p x y t : C^.obj}
    (base : C^.hom x t) (p₁ : C^.hom p x)
    (map : C^.hom y t)  (p₂ : C^.hom p y)
:= (has_pullback : HasPullback C (base ↗→ map ↗→↗))
   (ωpullback : @pullback C x [y] t _ has_pullback = p)
   (ωπ₁ : @pullback.π C x [y] t _ has_pullback (@fin_of 1 0) = p₁ ∘∘ cast_hom ωpullback)
   (ωπ₂ : @pullback.π C x [y] t _ has_pullback (@fin_of 0 1) = p₂ ∘∘ cast_hom ωpullback)

/-! #brief Pullback squares have the usual commutative diagram.
-/
theorem ispullback.square {C : Cat.{ℓobj ℓhom}}
    {p x y t : C^.obj}
    {base : C^.hom x t} {p₁ : C^.hom p x}
    {map : C^.hom y t}  {p₂ : C^.hom p y}
    (isPullback : IsPullback base p₁ map p₂)
    : C^.circ base p₁ = C^.circ map p₂
:= sorry

/-! #brief The universal map into a pullback square.
-/
definition ispullback.univ {C : Cat.{ℓobj ℓhom}}
    {p x y t : C^.obj}
    {base : C^.hom x t} {p₁ : C^.hom p x}
    {map : C^.hom y t}  {p₂ : C^.hom p y}
    (isPullback : IsPullback base p₁ map p₂)
    {c : C^.obj} (h₁ : C^.hom c x) (h₂ : C^.hom c y)
    (ωsquare : C^.circ base h₁ = C^.circ map h₂)
    : C^.hom c p
:= C^.circ
    (cast_hom (IsPullback.ωpullback base p₁ map p₂))
    (@pullback.univ _ _ _ _ _ (IsPullback.has_pullback base p₁ map p₂)
      (PullbackCone.mk _ c (C^.circ base h₁) (h₁ ↗← h₂ ↗←↗)
        begin
          apply dlist.eq,
          { trivial },
          apply dlist.eq,
          { exact ωsquare },
          trivial
        end))

/-! #brief Helper for showing one has a pullback square.
-/
definition IsPullback.show {C : Cat.{ℓobj ℓhom}}
    {p x y t : C^.obj}
    {base : C^.hom x t} {p₁ : C^.hom p x}
    {map : C^.hom y t}  {p₂ : C^.hom p y}
    (univ
      : ∀ {c : C^.obj} (h₁ : C^.hom c x) (h₂ : C^.hom c y)
          (ωsquare : C^.circ base h₁ = C^.circ map h₂)
        , C^.hom c p)
    (ωsquare
      : C^.circ base p₁ = C^.circ map p₂)
    (ωuniv₁
      : ∀ {c : C^.obj} (h₁ : C^.hom c x) (h₂ : C^.hom c y)
          (ωsquare : C^.circ base h₁ = C^.circ map h₂)
        , h₁ = C^.circ p₁ (univ h₁ h₂ ωsquare))
    (ωuniv₂
      : ∀ {c : C^.obj} (h₁ : C^.hom c x) (h₂ : C^.hom c y)
          (ωsquare : C^.circ base h₁ = C^.circ map h₂)
        , h₂ = C^.circ p₂ (univ h₁ h₂ ωsquare))
    (ωuniv_uniq
      : ∀ {c : C^.obj} (h₁ : C^.hom c x) (h₂ : C^.hom c y)
          (ωsquare : C^.circ base h₁ = C^.circ map h₂)
          (univ' : C^.hom c p)
          (ωuniv'₁ : h₁ = C^.circ p₁ univ')
          (ωuniv'₂ : h₂ = C^.circ p₂ univ')
        , univ' = univ h₁ h₂ ωsquare)
    : IsPullback base p₁ map p₂
:= { has_pullback
      := HasPullback.show C (base ↗→ map ↗→↗) p
          (C^.circ base p₁)
          (p₁ ↗← p₂ ↗←↗)
          begin
            apply dlist.eq,
            { trivial },
            apply dlist.eq,
            { exact ωsquare },
            trivial
          end
          (λ c homs ωhoms
           , begin
               cases homs with _ h₁ _ homs,
               cases homs with _ h₂ _ _,
               cases bb,
               apply univ h₁ h₂,
               apply HomsList.congr_get ωhoms (@fin_of 0 1)
             end)
          (λ c homs ωhoms
           , begin
               cases homs with _ h₁ _ homs,
               cases homs with _ h₂ _ _,
               cases bb,
               apply dlist.eq,
               { apply ωuniv₁ },
               apply dlist.eq,
               { apply ωuniv₂ },
               trivial
             end)
          (λ c homs ωhoms h ωh
           , begin
               cases homs with _ h₁ _ homs,
               cases homs with _ h₂ _ _,
               cases bb,
               apply ωuniv_uniq,
               { apply dlist.congr_get ωh (@fin_of 1 0) },
               { apply dlist.congr_get ωh (@fin_of 0 1) }
             end)
   , ωpullback := rfl
   , ωπ₁ := eq.symm C^.circ_id_right
   , ωπ₂ := eq.symm C^.circ_id_right
   }



/- -----------------------------------------------------------------------
Maps between pullbacks.
----------------------------------------------------------------------- -/

/-! #brief Building a map between pullbacks.
-/
definition pullback.hom (C : Cat.{ℓobj ℓhom})
    (base : C^.obj × C^.obj) (factor : list (C^.obj × C^.obj)) {t : C^.obj}
    (maps₁ : HomsIn (list.map prod.fst (base :: factor)) t)
    [maps₁_HasPullback : HasPullback C maps₁]
    (maps₂ : HomsIn (list.map prod.snd (base :: factor)) t)
    [maps₂_HasPullback : HasPullback C maps₂]
    (fns : HomsList C (base :: factor))
    : C^.hom (pullback C maps₁)
             (pullback C maps₂)
:= pullback.univ _ _
    (PullbackCone.mk maps₂ (pullback C maps₁)
      (HomsIn.get maps₂ fin.zero
        ∘∘ HomsList.get fns fin.zero
        ∘∘ pullback.π C maps₁ fin.zero)
      (homs_comp_out fns (pullback.cone C maps₁)^.Proj)
      sorry)



/- -----------------------------------------------------------------------
Base change.
----------------------------------------------------------------------- -/

/-! #brief A base change functor.
-/
definition BaseChangeFun {C : Cat.{ℓobj ℓhom}}
    {x y : C^.obj}
    (f : C^.hom x y)
    [f_HasPullbacksAlong : HasPullbacksAlong C f]
    : Fun (OverCat C y) (OverCat C x)
:= { obj := λ Y, { obj := pullback C (f ↗→ Y^.hom ↗→↗)
                 , hom := pullback.π C (f ↗→ Y^.hom ↗→↗) (@fin_of 1 0)
                 }
   , hom := λ X Y h, { hom := pullback.hom C
                               (x, x) [(X^.obj, Y^.obj)]
                               (f ↗→ X^.hom ↗→↗)
                               (f ↗→ Y^.hom ↗→↗)
                               (C^.id x ↗ h^.hom ↗↗)
                     , triangle := sorry
                     }
   , hom_id := λ Y, OverHom.eq sorry
   , hom_circ := λ X Y Z G F, OverHom.eq sorry
   }

/-! #brief The dependent sum functor.
-/
definition DepSumFun {C : Cat.{ℓobj ℓhom}}
    {x y : C^.obj}
    (f : C^.hom x y)
    : Fun (OverCat C x) (OverCat C y)
:= { obj := λ X
            , { obj := X^.obj
              , hom := C^.circ f X^.hom
              }
   , hom := λ X Y F
            , { hom := F^.hom
              , triangle
                 := begin
                      rw -C^.circ_assoc,
                      exact Cat.circ.congr_right  F^.triangle
                    end
              }
   , hom_id := λ X, rfl
   , hom_circ := λ X Y Z G F, rfl
   }

/-! #brief Dependent sum is adjoint to base change.
-/
definition DepSum_BaseChange.Adj {C : Cat.{ℓobj ℓhom}}
    {x y : C^.obj}
    (f : C^.hom x y)
    [f_HasPullbacksAlong : HasPullbacksAlong C f]
    : Adj (DepSumFun f) (BaseChangeFun f)
:= { counit
      := { com := λ Y, { hom := pullback.π C (f ↗→ Y^.hom ↗→↗) (@fin_of 0 1)
                       , triangle := sorry
                       }
         , natural := sorry
         }
   , unit
      := { com := λ X, { hom := pullback.univ C (f ↗→ (f ∘∘ X^.hom) ↗→↗)
                                  (PullbackCone.mk (f ↗→ (f ∘∘ X^.hom) ↗→↗)
                                    X^.dom
                                    (f ∘∘ X^.hom)
                                    (X^.hom ↗← ⟨⟨ X^.obj ⟩⟩ ↗←↗)
                                    begin
                                      apply dlist.eq,
                                      { trivial },
                                      apply dlist.eq,
                                      { rw [-C^.circ_assoc, C^.circ_id_right] },
                                      trivial
                                    end)
                       , triangle := sorry
                       }
         , natural := sorry
         }
   , id_left
      := λ c
         , OverHom.eq
            begin
              dsimp [OverCat, OverHom.id, OverHom.comp, DepSumFun],
              exact sorry
            end
   , id_right
      := λ c
         , OverHom.eq
            begin
              exact sorry
            end
   }

/-! #brief A category with dependent products.
-/
class HasDepProdFun (C : Cat.{ℓobj ℓhom})
:= (depprod
     : ∀ {x y : C^.obj} (f : C^.hom x y)
       , Fun (OverCat C x) (OverCat C y))
   (adj
     : ∀ {x y : C^.obj} (f : C^.hom x y)
         [f_HasPullbacksAlong : HasPullbacksAlong C f]
       , Adj (BaseChangeFun f) (depprod f))

/-! #brief A dependent product functor.
-/
definition DepProdFun {C : Cat.{ℓobj ℓhom}}
    [C_HasDepProdFun : HasDepProdFun C]
    {x y : C^.obj}
    (f : C^.hom x y)
    : Fun (OverCat C x) (OverCat C y)
:= HasDepProdFun.depprod f

/-! #brief Base change is adjoint to dependent product.
-/
definition BaseChange_DepProd.Adj {C : Cat.{ℓobj ℓhom}}
    [C_HasDepProdFun : HasDepProdFun C]
    {x y : C^.obj}
    (f : C^.hom x y)
    [f_HasPullbacksAlong : HasPullbacksAlong C f]
    : Adj (BaseChangeFun f) (DepProdFun f)
:= HasDepProdFun.adj f



/- -----------------------------------------------------------------------
Pullbacks along final homs.
----------------------------------------------------------------------- -/

/-! Categories with products have pullbacks along final homs.
-/
instance HasAllFinProducts.final_hom.HasPullbacksAlong
    {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    [C_HasAllFinProducts : HasAllFinProducts C]
    (x : C^.obj)
    : HasPullbacksAlong C (final_hom x)
:= { has_pullback
      := λ y map
         , HasPullback.show C (final_hom x ↗→ map ↗→↗)
            (finproduct C [x, y])
            (final_hom (finproduct C [x, y]))
            (finproduct.cone C [x, y])^.Proj
            begin
              apply eq.symm,
              apply dlist.eq,
              { apply final_hom.uniq },
              -- induction maps with _ m _ maps rec,
              -- { trivial },
              -- apply dlist.eq,
              -- { apply final_hom.uniq },
              -- apply rec
              exact sorry
            end
            begin exact sorry end
            begin exact sorry end
            begin exact sorry end
   }

end qp
