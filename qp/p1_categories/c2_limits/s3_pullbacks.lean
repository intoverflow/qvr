/- -----------------------------------------------------------------------
Pullbacks and pushouts.
----------------------------------------------------------------------- -/

import .s1_limits
import .s2_products

namespace qp

open stdaux

universe variables ℓobjx ℓhomx ℓobj ℓhom ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂



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

/-! #brief Functor which forgets the base hom.
-/
definition CoSpanCat.forget_base (N : ℕ)
    : Fun (CoSpanCat N) (CoSpanCat (nat.succ N))
:= { obj := λ n, option.cases_on n option.none (λ n', option.some (stdaux.fin.add n' 1))
   , hom := λ x y f
            , begin
                cases f,
                { apply CoSpanHom.id },
                { apply CoSpanHom.hom }
              end
   , hom_id := λ x, rfl
   , hom_circ := λ x y z g f
                 , begin
                     cases f,
                     { trivial },
                     { cases g, trivial }
                   end
   }

/-! #brief A cospan diagram.
-/
definition PullbackDrgm (C : Cat.{ℓobj ℓhom})
    {factor : list C^.obj} {t : C^.obj}
    (maps : HomsIn factor t)
    : Fun (CoSpanCat (list.length factor)) C
:= { obj := λ a, option.cases_on a t (list.get factor)
   , hom := λ a₁ a₂ f, begin cases f, { apply C^.id }, { exact HomsIn.get maps n } end
   , hom_id := λ a, rfl
   , hom_circ := λ a₁ a₂ a₃ g f
                 , begin
                     cases f,
                     { apply eq.symm C^.circ_id_right },
                     { cases g, apply eq.symm C^.circ_id_left }
                   end
   }

/-! #brief Every functor out of CoSpanCat is a PullbackDrgm.
-/
definition PullbackDrgm.mk_doms {C : Cat.{ℓobj ℓhom}}
    : ∀ {N : ℕ}
        (F : Fun (CoSpanCat N) C)
      , list C^.obj
| 0 F := []
| (nat.succ N) F := (F^.obj (some (fin_of 0))) :: @PullbackDrgm.mk_doms N (F □□ CoSpanCat.forget_base N)

/-! #brief Every functor out of CoSpanCat is a PullbackDrgm.
-/
theorem PullbackDrgm.length_mk_doms {C : Cat.{ℓobj ℓhom}}
    : ∀ {N : ℕ}
        (F : Fun (CoSpanCat N) C)
      , list.length (PullbackDrgm.mk_doms F) = N
| 0 F := rfl
| (nat.succ N) F := congr_arg nat.succ (@PullbackDrgm.length_mk_doms N (F □□ CoSpanCat.forget_base N))

/-! #brief Every functor out of CoSpanCat is a PullbackDrgm.
-/
definition PullbackDrgm.mk_homs {C : Cat.{ℓobj ℓhom}}
    : ∀ {N : ℕ}
        (F : Fun (CoSpanCat N) C)
      , @HomsIn C (PullbackDrgm.mk_doms F) (F^.obj none)
| 0 F := HomsIn.nil
| (nat.succ N) F
:= HomsIn.cons (F^.hom (CoSpanHom.hom (fin_of 0)))
               (@PullbackDrgm.mk_homs N (F □□ CoSpanCat.forget_base N))

/-! #brief Every functor out of CoSpanCat is a PullbackDrgm.
-/
theorem PullbackDrgm.uniq {C : Cat.{ℓobj ℓhom}}
    {N : ℕ}
    (F : Fun (CoSpanCat N) C)
    : PullbackDrgm C (PullbackDrgm.mk_homs F) == F
:= begin
     apply Fun.heq,
     { exact congr_arg CoSpanCat (PullbackDrgm.length_mk_doms F) },
     { trivial },
     { intros n₁ n₂ ωn,
       dsimp [PullbackDrgm],
       cases n₁ with n₁ ωn₁,
       { cases n₂ with n₂ ωn₂,
         { trivial },
         { exact sorry } -- TODO
       },
       { cases n₂ with n₂ ωn₂,
         { exact sorry }, -- TODO
         { exact sorry } -- TODO
       } 
     },
     { intros x₁ y₁ x₂ y₂ f₁ f₂ ωf,
       cases f₁,
       { cases f₂,
         { exact sorry }, -- TODO
         { exact sorry } -- TODO
       },
       { cases f₂,
         { exact sorry }, -- TODO
         { exact sorry } -- TODO
       }
     }
   end

/-! #brief A cone over a pullback.
-/
definition PullbackCone (C : Cat.{ℓobj ℓhom})
    {factor : list C^.obj} {t : C^.obj}
    (maps : HomsIn factor t)
    : Type (max ℓobj ℓhom)
:= Cone (PullbackDrgm C maps)

/-! #brief Helper for making a pullback cone.
-/
definition PullbackCone.mk {C : Cat.{ℓobj ℓhom}}
    {factor : list C^.obj} {t : C^.obj}
    (maps : HomsIn factor t)
    (c : C^.obj)
    (to_t : C^.hom c t)
    (proj : HomsOut c factor)
    (ωproj : HomsList.repeat to_t (list.length factor)
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
    {factor : list C^.obj} {t : C^.obj}
    {maps : HomsIn factor t}
    (cone : PullbackCone C maps)
    : HomsOut cone^.obj factor
:= sorry -- HomsOut.enum (Cone.hom cone)

/-! #brief A pullback in a category.
-/
@[class] definition HasPullback (C : Cat.{ℓobj ℓhom})
    {factor : list C^.obj} {t : C^.obj}
    (maps : HomsIn factor t)
:= HasLimit (PullbackDrgm C maps)

instance HasPullback.HasLimit {C : Cat.{ℓobj ℓhom}}
    {factor : list C^.obj} {t : C^.obj}
    (maps : HomsIn factor t)
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

instance HasAllPullbacks.HasAllLimitsFrom (C : Cat.{ℓobj ℓhom})
    [C_HasAllPullbacks : HasAllPullbacks C]
    (N : ℕ)
    : HasAllLimitsFrom C (CoSpanCat (nat.succ N))
:= { has_limit := λ L, let l := HasAllPullbacks.HasPullback C (PullbackDrgm.mk_homs L)
                       in cast (HasLimit.heq begin rw PullbackDrgm.length_mk_doms end rfl (PullbackDrgm.uniq L)) l
   }

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

instance HasAllPullbacks.HasPullbacksAlong (C : Cat.{ℓobj ℓhom})
    [C_HasAllPullbacks : HasAllPullbacks C]
    {base t : C^.obj} (f : C^.hom base t)
    : HasPullbacksAlong C f
:= { has_pullback := λ y map, HasAllPullbacks.has_pullback (f ↗→ map ↗→↗)
   }

/-! #brief Helper for showing a category has a pullback.
-/
definition HasPullback.show (C : Cat.{ℓobj ℓhom})
    {factor : list C^.obj} {t : C^.obj}
    (maps : HomsIn factor t)
    (p : C^.obj)
    (to_t : C^.hom p t)
    (proj : HomsOut p factor)
    (ωproj : HomsList.repeat to_t (list.length factor)
              = homs_in_comp_out maps proj)
    (univ : ∀ {c : C^.obj} (to_t' : C^.hom c t) (hom : HomsOut c factor)
              (ωhom : HomsList.repeat
                       to_t'
                       (list.length factor)
                       = homs_in_comp_out maps hom)
            , C^.hom c p)
    (ωuniv : ∀ {c : C^.obj} (to_t' : C^.hom c t) (hom : HomsOut c factor)
              (ωhom : HomsList.repeat
                       to_t'
                       (list.length factor)
                       = homs_in_comp_out maps hom)
             , hom = HomsOut.comp proj (univ to_t' hom ωhom))
    (ωuniq : ∀ {c : C^.obj} (to_t' : C^.hom c t) (hom : HomsOut c factor)
              (ωhom : HomsList.repeat
                       to_t'
                       (list.length factor)
                       = homs_in_comp_out maps hom)
               (h : C^.hom c p)
               (ωcomm : hom = HomsOut.comp proj h)
             , h = univ to_t' hom ωhom)
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
    (λ c hom ωcomm, univ (hom none) (HomsOut.enum (λ n, hom (some n)))
     begin
       exact sorry
     end)
    (λ c hom ωcomm a, begin exact sorry end)
    (λ c hom ωcomm h ωh, begin exact sorry end)

/-! #brief Pullbacks are cones.
-/
definition pullback.cone (C : Cat.{ℓobj ℓhom})
    {factor : list C^.obj} {t : C^.obj}
    (maps : HomsIn factor t)
    [maps_HasPullback : HasPullback C maps]
    : PullbackCone C maps
:= limit.cone (PullbackDrgm C maps)

/-! #brief The pullback of a collection of homs.
-/
definition pullback (C : Cat.{ℓobj ℓhom})
    {factor : list C^.obj} {t : C^.obj}
    (maps : HomsIn factor t)
    [maps_HasPullback : HasPullback C maps]
    : C^.obj
:= limit (PullbackDrgm C maps)

/-! #brief Projection out of a pullback.
-/
definition pullback.π (C : Cat.{ℓobj ℓhom})
    {factor : list C^.obj} {t : C^.obj}
    (maps : HomsIn factor t)
    [maps_HasPullback : HasPullback C maps]
    (n : fin (list.length factor))
    : C^.hom (pullback C maps) (list.get factor n)
:= limit.out (PullbackDrgm C maps) (some n)

/-! #brief The commutative square property of pullbacks.
-/
definition pullback.π_comm (C : Cat.{ℓobj ℓhom})
    {factor : list C^.obj} {t : C^.obj}
    (maps : HomsIn factor t)
    [maps_HasPullback : HasPullback C maps]
    (n₁ n₂ : fin (list.length factor))
    : HomsIn.get maps n₁ ∘∘ pullback.π C maps n₁
       = HomsIn.get maps n₂ ∘∘ pullback.π C maps n₂
:= sorry

/-! #brief Projection out of a pullback to the base.
-/
definition pullback.πbase (C : Cat.{ℓobj ℓhom})
    {factor : list C^.obj} {t : C^.obj}
    (maps : HomsIn factor t)
    [maps_HasPullback : HasPullback C maps]
    : C^.hom (pullback C maps) t
:= limit.out (PullbackDrgm C maps) none

/-! #brief Every cone is mediated through the pullback.
-/
definition pullback.univ (C : Cat.{ℓobj ℓhom})
    {factor : list C^.obj} {t : C^.obj}
    (maps : HomsIn factor t)
    [maps_HasPullback : HasPullback C maps]
    (c : PullbackCone C maps)
    : C^.hom c^.obj (pullback C maps)
:= limit.univ _ c

/-! #brief Every cone is mediated through the pullback.
-/
definition pullback.univ.mediates (C : Cat.{ℓobj ℓhom})
    {factor : list C^.obj} {t : C^.obj}
    (maps : HomsIn factor t)
    {maps_HasPullback : HasPullback C maps}
    (c : PullbackCone C maps)
    (n : fin (list.length factor))
    : c^.hom (some n) = C^.circ (@pullback.π C factor t maps maps_HasPullback n) (pullback.univ C maps c)
:= limit.univ.mediates c (some n)

/-! #brief Every cone is mediated through the pullback.
-/
definition pullback.univ.mediates_base (C : Cat.{ℓobj ℓhom})
    {factor : list C^.obj} {t : C^.obj}
    (maps : HomsIn factor t)
    {maps_HasPullback : HasPullback C maps}
    (c : PullbackCone C maps)
    : c^.hom none = C^.circ (@pullback.πbase C factor t maps maps_HasPullback) (pullback.univ C maps c)
:= limit.univ.mediates c none

/-! #brief The mediating map from the cone to the pullback is unique.
-/
definition pullback.univ.uniq (C : Cat.{ℓobj ℓhom})
    {factor : list C^.obj} {t : C^.obj}
    (maps : HomsIn factor t)
    {maps_HasPullback : HasPullback C maps}
    (c : PullbackCone C maps)
    (m : C^.hom c^.obj (pullback C maps))
    (ω : ∀ (n : fin (list.length factor))
         , c^.hom (some n) = (@pullback.π C factor t maps maps_HasPullback n) ∘∘ m)
    (ωbase : c^.hom none = (@pullback.πbase C factor t maps maps_HasPullback) ∘∘ m)
    : m = pullback.univ C maps c
:= limit.univ.uniq c m (λ x, option.cases_on x ωbase ω)

/-! #brief The unique iso between two pullbacks of the same homs.
-/
definition pullback.iso {C : Cat.{ℓobj ℓhom}}
    {factor : list C^.obj} {t : C^.obj}
    {maps : HomsIn factor t}
    (maps_HasPullback₁ maps_HasPullback₂ : HasPullback C maps)
    : C^.hom (@pullback C factor t maps maps_HasPullback₁)
             (@pullback C factor t maps maps_HasPullback₂)
:= limit.iso maps_HasPullback₁ maps_HasPullback₂

/-! #brief Pullbacks are unique up-to unique isomorphism.
-/
definition pullback.uniq {C : Cat.{ℓobj ℓhom}}
    {factor : list C^.obj} {t : C^.obj}
    {maps : HomsIn factor t}
    (maps_HasPullback₁ maps_HasPullback₂ : HasPullback C maps)
    : Iso (pullback.iso maps_HasPullback₁ maps_HasPullback₂)
          (pullback.iso maps_HasPullback₂ maps_HasPullback₁)
:= limit.uniq maps_HasPullback₁ maps_HasPullback₂



/- -----------------------------------------------------------------------
Pullbacks in functor categories.
----------------------------------------------------------------------- -/

/-! #brief Pullbacks in functor categories can be computed pointwise.
-/
instance FunCat.HasPullback {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    [D_HasAllPullbacks : HasAllPullbacks D]
    {base : Fun C D} {factor : list (Fun C D)} {t : Fun C D}
    (maps : @HomsIn (FunCat C D) (base :: factor) t)
    : HasPullback (FunCat C D) maps
:= @FunCat.HasLimit _ _ _ (HasAllPullbacks.HasAllLimitsFrom D _) (PullbackDrgm (FunCat C D) maps)

/-! #brief Pullbacks in functor categories can be computed pointwise.
-/
instance FunCat.HasAllPullbacks {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    [D_HasAllPullbacks : HasAllPullbacks D]
    : HasAllPullbacks (FunCat C D)
:= { has_pullback := λ base factor t maps, FunCat.HasPullback maps
   }



/- -----------------------------------------------------------------------
Pullback squares.
----------------------------------------------------------------------- -/

/-! #brief A pullback square.
-/
class IsPullback {C : Cat.{ℓobj ℓhom}}
    {p x y t : C^.obj}
    (base : C^.hom x t) (p₁ : C^.hom p x)
    (map : C^.hom y t)  (p₂ : C^.hom p y)
:= (has_pullback : HasPullback C (base ↗→ map ↗→↗))
   (ωpullback : @pullback C [x, y] t _ has_pullback = p)
   (ωπ₁ : @pullback.π C [x, y] t _ has_pullback (@fin_of 1 0) = p₁ ∘∘ cast_hom ωpullback)
   (ωπ₂ : @pullback.π C [x, y] t _ has_pullback (@fin_of 0 1) = p₂ ∘∘ cast_hom ωpullback)

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
    (@pullback.univ _ _ _ _ (IsPullback.has_pullback base p₁ map p₂)
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
          (λ c to_t homs ωhoms
           , begin
               cases homs with _ h₁ _ homs,
               cases homs with _ h₂ _ _,
               cases bb,
               apply univ h₁ h₂,
               refine @eq.trans _  _ to_t _  _ _,
               { apply eq.symm,
                 apply HomsList.congr_get ωhoms (@fin_of 1 0)
               },
               { apply HomsList.congr_get ωhoms (@fin_of 0 1) }
             end)
          (λ c to_t homs ωhoms
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
          (λ c to_t homs ωhoms h ωh
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
Maps from pullbacks to products.
----------------------------------------------------------------------- -/

/-! #brief The map from a pullback to the underlying product.
-/
definition pullback.to_finproduct (C : Cat.{ℓobj ℓhom})
    {factor : list C^.obj} {t : C^.obj}
    (maps : HomsIn factor t)
    [maps_HasPullback : HasPullback C maps]
    [dom_HasFinProduct : HasFinProduct C factor]
    : C^.hom (pullback C maps) (finproduct C factor)
:= sorry


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
Fibers.
----------------------------------------------------------------------- -/

/-! #brief Fiber of a map over a global element.
-/
definition Fiber {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    {x y : C^.obj} (f : C^.hom x y)
    (y₀ : C^.hom (final C) y)
    : C^.obj
:= pullback C (f ↗→ y₀ ↗→↗)

/-! #brief Projection out of a fiber.
-/
definition Fiber.π {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    {x y : C^.obj} (f : C^.hom x y)
    (y₀ : C^.hom (final C) y)
    : C^.hom (Fiber f y₀) x
:= pullback.π C (f ↗→ y₀ ↗→↗) (@fin_of 1 0)

/-! #brief A hom into a fiber.
-/
definition Fiber.into {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    {x y : C^.obj} (f : C^.hom x y)
    (y₀ : C^.hom (final C) y)
    {z : C^.obj}
    (h : C^.hom z x)
    (ωh : f ∘∘ h = y₀ ∘∘ final_hom z)
    : C^.hom z (Fiber f y₀)
:= pullback.univ C (f ↗→ y₀ ↗→↗)
    (PullbackCone.mk (f ↗→ y₀ ↗→↗) z
      (C^.circ f h)
      (h ↗← final_hom z ↗←↗)
      begin
        apply HomsList.eq, { trivial },
        apply HomsList.eq, { exact ωh },
        trivial
      end)

/-! #brief A cone over a fiber.
-/
definition Fiber.cone {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    {x₁ x₂ y : C^.obj} {f₁ : C^.hom x₁ y} {f₂ : C^.hom x₂ y}
    {y₀ : C^.hom (final C) y}
    (h : C^.hom x₁ x₂)
    (ωh : y₀ ∘∘ final_hom (Fiber f₁ y₀)
           = f₂ ∘∘ h ∘∘ pullback.π C (f₁ ↗→ y₀ ↗→↗) (@fin_of 1 0))
:= PullbackCone.mk (f₂ ↗→ y₀ ↗→↗) (Fiber f₁ y₀)
      (y₀ ∘∘ final_hom (Fiber f₁ y₀))
      (h ∘∘ pullback.π C (f₁ ↗→ y₀ ↗→↗) (@fin_of 1 0) ↗← final_hom (Fiber f₁ y₀) ↗←↗)
      begin
        apply HomsList.eq, { exact eq.trans ωh (eq.symm C^.circ_assoc) },
        apply HomsList.eq, { trivial },
        trivial
      end

/-! #brief A hom between fibers.
-/
definition Fiber.hom {C : Cat.{ℓobj ℓhom}}
    [C_HasFinal : HasFinal C]
    [C_HasAllPullbacks : HasAllPullbacks C]
    {x₁ x₂ y : C^.obj} {f₁ : C^.hom x₁ y} {f₂ : C^.hom x₂ y}
    {y₀ : C^.hom (final C) y}
    (h : C^.hom x₁ x₂)
    (ωh : y₀ ∘∘ final_hom (Fiber f₁ y₀)
           = f₂ ∘∘ h ∘∘ pullback.π C (f₁ ↗→ y₀ ↗→↗) (@fin_of 1 0))
    : C^.hom (Fiber f₁ y₀) (Fiber f₂ y₀)
:= pullback.univ C (f₂ ↗→ y₀ ↗→↗) (Fiber.cone h ωh)



/- -----------------------------------------------------------------------
Products in OverCat.
----------------------------------------------------------------------- -/

/-! #brief Existence of products in an over-category.
-/
definition OverCat.HasFinProduct₀ (C : Cat.{ℓobj ℓhom}) (c : C^.obj)
    : HasFinProduct (OverCat C c) []
:= @HasFinProduct.show (OverCat C c) []
    (@final (OverCat C c) (OverCat.HasFinal C c))
    HomsOut.nil
    (λ X homs, @final_hom (OverCat C c) (OverCat.HasFinal C c) X)
    (λ X homs, begin cases homs, trivial end)
    (λ X homs h ωh, @final_hom.uniq (OverCat C c) (OverCat.HasFinal C c) X h)

/-! #brief Existence of products in an over-category.
-/
definition OverCat.HasFinProduct₁ (C : Cat.{ℓobj ℓhom}) (c : C^.obj)
    (factors : list (OverCat C c)^.obj)
    [factors_HasPullback : HasPullback C (HomsIn.of_list_OverObj factors)]
    : HasFinProduct (OverCat C c) factors
:= let pb : OverObj C c
         := { obj := pullback C (HomsIn.of_list_OverObj factors)
            , hom := pullback.πbase C (HomsIn.of_list_OverObj factors)
            }
in HasProduct.show (OverCat C c) (list.get factors)
    pb
    (λ n, { hom := cast_hom sorry
                    ∘∘ pullback.π C (HomsIn.of_list_OverObj factors)
                        { val := n^.val, is_lt := cast sorry n^.is_lt }
          , triangle := sorry
          })
    (λ X homs
     , { hom := pullback.univ C (HomsIn.of_list_OverObj factors)
                 (PullbackCone.mk (HomsIn.of_list_OverObj factors) X^.obj
                   X^.hom
                   (HomsOut.enum
                     (λ n, cast_hom sorry
                            ∘∘ (homs { val := n^.val, is_lt := cast sorry n^.is_lt})^.hom))
                   sorry)
       , triangle := sorry
       })
    (λ X hom n, sorry)
    (λ X hom h ωh, sorry)

/-! #brief Existence of products in an over-category.
-/
instance OverCat.HasFinProduct (C : Cat.{ℓobj ℓhom}) (c : C^.obj)
    [C_HasAllPullbacks : HasAllPullbacks C]
    : ∀ (factors : list (OverCat C c)^.obj)
      , HasFinProduct (OverCat C c) factors
| [] := OverCat.HasFinProduct₀ C c
| (factor₀ :: factors)
:= @OverCat.HasFinProduct₁ C c (factor₀ :: factors)
     (HasAllPullbacks.HasPullback C _)

instance OverCat.HasAllFinProducts (C : Cat.{ℓobj ℓhom}) (c : C^.obj)
    [C_HasAllPullbacks : HasAllPullbacks C]
    : HasAllFinProducts (OverCat C c)
:= { has_product := OverCat.HasFinProduct C c
   }


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
