/- -----------------------------------------------------------------------
Pullbacks and pushouts.
----------------------------------------------------------------------- -/

import .s1_limits

namespace qp

open stdaux

universe variables ℓobj ℓhom --ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂



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
structure IsPullback {C : Cat.{ℓobj ℓhom}}
    {p x y t : C^.obj}
    (base : C^.hom x t) (p₁ : C^.hom p x)
    (map : C^.hom y t)  (p₂ : C^.hom p y)
:= (has_pullback : HasPullback C (base ↗→ map ↗→↗))
   (ωpullback : @pullback C x [y] t _ has_pullback = p)
   (ωπ₁ : @pullback.π C x [y] t _ has_pullback (@fin_of 1 0) = p₁ ∘∘ cast_hom ωpullback)
   (ωπ₂ : @pullback.π C x [y] t _ has_pullback (@fin_of 0 1) = p₂ ∘∘ cast_hom ωpullback)


end qp
