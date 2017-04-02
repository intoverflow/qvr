/- -----------------------------------------------------------------------
Limits and co-limits.
----------------------------------------------------------------------- -/

import ..c1_basic

namespace qp

open stdaux

universe variables ℓobjx ℓhomx ℓobj ℓhom ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂



/- -----------------------------------------------------------------------
Limits.
----------------------------------------------------------------------- -/

/-! #brief A limit of a functor.
-/
@[class] definition HasLimit {X : Cat.{ℓobjx ℓhomx}} {C : Cat.{ℓobj₁ ℓhom₁}}
    (L : Fun X C)
:= HasFinal (ConeCat L)

instance HasLimit.ConeCat_HasFinal {X : Cat.{ℓobjx ℓhomx}} {C : Cat.{ℓobj₁ ℓhom₁}}
    (L : Fun X C)
    [L_HasLimit : HasLimit L]
    : HasFinal (ConeCat L)
:= L_HasLimit

/-! #brief A category with all limits.
-/
class HasAllLimits (C : Cat.{ℓobj₁ ℓhom₁})
:= (has_limit : ∀ {X : Cat.{ℓobjx ℓhomx}} (L : Fun X C)
                , HasLimit L)

instance HasAllLimits.HasLimit {C : Cat.{ℓobj₁ ℓhom₁}}
    [C_HasAllLimits : HasAllLimits.{ℓobjx ℓhomx ℓobj₁ ℓhom₁} C]
    {X : Cat.{ℓobjx ℓhomx}} (L : Fun X C)
    : HasLimit L
:= HasAllLimits.has_limit L

/-! #brief A category with all limits out of another category.
-/
class HasAllLimitsFrom (C : Cat.{ℓobj₁ ℓhom₁}) (X : Cat.{ℓobjx ℓhomx})
:= (has_limit : ∀ (L : Fun X C), HasLimit L)

instance HasAllLimitsFrom.HasLimit (C : Cat.{ℓobj₁ ℓhom₁}) {X : Cat.{ℓobjx ℓhomx}}
    (L : Fun X C)
    [C_HasAllLimitsFrom_X : HasAllLimitsFrom C X]
    : HasLimit L
:= HasAllLimitsFrom.has_limit L

/-! #brief Helper for showing a functor has a limit.
-/
definition HasLimit.show {X : Cat.{ℓobjx ℓhomx}} {C : Cat.{ℓobj₁ ℓhom₁}}
    {L : Fun X C}
    (l : C^.obj)
    (out : ∀ (x : X^.obj), C^.hom l (L^.obj x))
    (ωout : ∀ {x₁ x₂ : X^.obj} (f : X^.hom x₁ x₂)
             , out x₂ = C^.circ (L^.hom f) (out x₁))
    (univ
      : ∀ (c : C^.obj)
          (hom : ∀ (x : X^.obj), C^.hom c (L^.obj x))
          (comm : ∀ {x₁ x₂ : X^.obj} (f : X^.hom x₁ x₂)
                  , hom x₂ = C^.circ (L^.hom f) (hom x₁))
        , C^.hom c l)
    (ωuniv
      : ∀ (c : C^.obj)
          (hom : ∀ (x : X^.obj), C^.hom c (L^.obj x))
          (comm : ∀ {x₁ x₂ : X^.obj} (f : X^.hom x₁ x₂)
                  , hom x₂ = C^.circ (L^.hom f) (hom x₁))
          (x : X^.obj)
        , hom x = C^.circ (out x) (univ c hom @comm))
    (ωuniq
      : ∀ (c : C^.obj)
          (hom : ∀ (x : X^.obj), C^.hom c (L^.obj x))
          (comm : ∀ {x₁ x₂ : X^.obj} (f : X^.hom x₁ x₂)
                  , hom x₂ = C^.circ (L^.hom f) (hom x₁))
          (f : C^.hom c l)
          (ωf : ∀ (x : X^.obj), hom x = C^.circ (out x) f)
        , f = univ c hom @comm)
    : HasLimit L
:= HasFinal.show
    { obj := l, hom := out, comm := @ωout }
    (λ cone, { mediate := univ cone^.obj cone^.hom (@Cone.comm _ _ _ cone)
             , factor := ωuniv cone^.obj cone^.hom (@Cone.comm _ _ _ cone)
             })
   (λ cone cone_hom
    , ConeHom.eq (ωuniq
                   cone^.obj cone^.hom (@Cone.comm _ _ _ cone)
                   cone_hom^.mediate cone_hom^.factor))

/-! #brief Limits are cones.
-/
definition limit.cone {X : Cat.{ℓobjx ℓhomx}} {C : Cat.{ℓobj₁ ℓhom₁}}
    (F : Fun X C)
    [F_HasLimit : HasLimit F]
    : Cone F
:= final (ConeCat F)

/-! #brief The limit object of a functor.
-/
definition limit {X : Cat.{ℓobjx ℓhomx}} {C : Cat.{ℓobj₁ ℓhom₁}}
    (F : Fun X C)
    [F_HasLimit : HasLimit F]
    : C^.obj
:= (limit.cone F)^.obj

/-! #brief A map out of the limit.
-/
definition limit.out {X : Cat.{ℓobjx ℓhomx}} {C : Cat.{ℓobj₁ ℓhom₁}}
    (F : Fun X C)
    [F_HasLimit : HasLimit F]
    (x : X^.obj)
    : C^.hom (limit F) (F^.obj x)
:= (final (ConeCat F))^.hom x

/-! #brief The limit-out maps commute with the diagram.
-/
theorem limit.out.comm {X : Cat.{ℓobjx ℓhomx}} {C : Cat.{ℓobj₁ ℓhom₁}}
    (F : Fun X C)
    [F_HasLimit : HasLimit F]
    {x₁ x₂ : X^.obj}
    (f : X^.hom x₁ x₂)
    : limit.out F x₂ = C^.circ (F^.hom f) (limit.out F x₁)
:= (final (ConeCat F))^.comm f

/-! #brief Every cone is mediated through the limit.
-/
definition limit.univ {X : Cat.{ℓobjx ℓhomx}} {C : Cat.{ℓobj₁ ℓhom₁}}
    {F : Fun X C}
    [F_HasLimit : HasLimit F]
    (c : Cone F)
    : C^.hom c^.obj (limit F)
:= (@final_hom (ConeCat F) _ c)^.mediate

/-! #brief Every cone is mediated through the limit.
-/
theorem limit.univ.mediates {X : Cat.{ℓobjx ℓhomx}} {C : Cat.{ℓobj₁ ℓhom₁}}
    {F : Fun X C}
    {F_HasLimit : HasLimit F}
    (c : Cone F)
    (x : X^.obj)
    : c^.hom x = C^.circ (limit.out F x) (limit.univ c)
:= (@final_hom (ConeCat F) _ c)^.factor x

/-! #brief The mediating map from a cone to the limit is unique.
-/
theorem limit.univ.uniq {X : Cat.{ℓobjx ℓhomx}} {C : Cat.{ℓobj₁ ℓhom₁}}
    {F : Fun X C}
    {F_HasLimit : HasLimit F}
    (c : Cone F)
    (m : C^.hom c^.obj (limit F))
    (ω : ∀ (x : X^.obj), c^.hom x = limit.out F x ∘∘ m)
    : m = limit.univ c
:= let m' : ConeHom F c (limit.cone F)
         := { mediate := m
            , factor := ω
            } in
   let ωm' : m' = @final_hom (ConeCat F) _ c
          := final_hom.uniq (ConeCat F)
   in congr_arg ConeHom.mediate ωm'

/-! #brief The unique iso between two limits of the same functor.
-/
definition limit.iso {X : Cat.{ℓobjx ℓhomx}} {C : Cat.{ℓobj₁ ℓhom₁}}
    {F : Fun X C}
    (F_HasLimit₁ F_HasLimit₂ : HasLimit F)
    : C^.hom (@limit X C F F_HasLimit₁) (@limit X C F F_HasLimit₂)
:= @limit.univ X C F F_HasLimit₂ (@limit.cone X C F F_HasLimit₁)

/-! #brief Limits are unique up-to unique isomorphism.
-/
theorem limit.uniq {X : Cat.{ℓobjx ℓhomx}} {C : Cat.{ℓobj₁ ℓhom₁}}
    {F : Fun X C}
    (F_HasLimit₁ F_HasLimit₂ : HasLimit F)
    : Iso (limit.iso F_HasLimit₁ F_HasLimit₂)
          (limit.iso F_HasLimit₂ F_HasLimit₁)
:= { id₁ := eq.trans (eq.symm ConeHom.comp.simp_mediate)
                     (congr_arg ConeHom.mediate (HasFinal_uniq F_HasLimit₁ F_HasLimit₂)^.id₁)
   , id₂ := eq.trans (eq.symm ConeHom.comp.simp_mediate)
                     (congr_arg ConeHom.mediate (HasFinal_uniq F_HasLimit₁ F_HasLimit₂)^.id₂)
   }



/- -----------------------------------------------------------------------
Preservation of limits by functors.
----------------------------------------------------------------------- -/

/-! #brief A functor which preserves a limit.
-/
@[class] definition PresLimit {X : Cat.{ℓobjx ℓhomx}} {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    (L : Fun X B)
    (F : Fun B C)
:= PresFinal (LeftConeFun F L)

/-! #brief A functor which preserves colimits out of a given category.
-/
class PresLimitsFrom {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    (F : Fun B C)
    (X : Cat.{ℓobjx ℓhomx})
:= (pres_limit : ∀ (L : Fun X B)
                 , PresLimit L F)

instance PresLimitsFrom.PresLimit {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    (F : Fun B C)
    {X : Cat.{ℓobjx ℓhomx}}
    [F_PresLimitsFrom : PresLimitsFrom F X]
    (L : Fun X B)
    : PresLimit L F
:= PresLimitsFrom.pres_limit F L

/-! #brief Functors which preserve limits yield instances of HasLimit.
-/
instance PresLimit.HasLimit {X : Cat.{ℓobjx ℓhomx}} {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    (L : Fun X B) [L_HasLimit : HasLimit L]
    (F : Fun B C) [F_PresLimit : PresLimit L F]
    : HasLimit (Fun.comp F L)
:= @PresFinal.HasFinal _ _ L_HasLimit (LeftConeFun F L) F_PresLimit

/-! #brief Helper for showing that a functor preserves a limit.
-/
definition PresLimit.show {X : Cat.{ℓobjx ℓhomx}} {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {L : Fun X B}
    {F : Fun B C}
    (mediate
      : ∀ [L_HasLimit : HasLimit L]
          (c : C^.obj)
          (hom : ∀ (x : X^.obj), C^.hom c (F^.obj (L^.obj x)))
          (ωcomm : ∀ {x₁ x₂ : X^.obj} (f : X^.hom x₁ x₂)
                   , hom x₂ = C^.circ (F^.hom (L^.hom f)) (hom x₁))
        , C^.hom c (F^.obj (limit L)))
    (ωmediate
      : ∀ [L_HasLimit : HasLimit L]
          (c : C^.obj)
          (hom : ∀ (x : X^.obj), C^.hom c (F^.obj (L^.obj x)))
          (ωcomm : ∀ {x₁ x₂ : X^.obj} (f : X^.hom x₁ x₂)
                   , hom x₂ = C^.circ (F^.hom (L^.hom f)) (hom x₁))
          (x : X^.obj)
        , hom x = F^.hom (limit.out L x) ∘∘ mediate c hom @ωcomm)
    (ωuniq
      : ∀ [L_HasLimit : HasLimit L]
          (c : C^.obj)
          (hom : ∀ (x : X^.obj), C^.hom c (F^.obj (L^.obj x)))
          (ωcomm : ∀ {x₁ x₂ : X^.obj} (f : X^.hom x₁ x₂)
                   , hom x₂ = C^.circ (F^.hom (L^.hom f)) (hom x₁))
          (f : C^.hom c (F^.obj (limit L)))
          (ωf : ∀ (x : X^.obj), hom x = C^.circ (F^.hom (limit.out L x)) f)
        , f = mediate c hom @ωcomm)
    : PresLimit L F
:= { hom := λ L_HasLimit cone
            , { mediate := @mediate L_HasLimit cone^.obj cone^.hom (@Cone.comm _ _ _ cone)
              , factor := @ωmediate L_HasLimit cone^.obj cone^.hom (@Cone.comm _ _ _ cone)
              }
   , pres := λ L_HasLimit
             , { hom_uniq := λ cone h, ConeHom.eq (@ωuniq L_HasLimit cone^.obj cone^.hom (@Cone.comm _ _ _ cone)
                                                     h^.mediate h^.factor)
               }
   }

/-! #brief A limit of a functor.
-/
theorem preslimit {X : Cat.{ℓobjx ℓhomx}} {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    (L : Fun X B) [L_HasLimit : HasLimit L]
    (F : Fun B C) [F_PresLimit : PresLimit L F]
    : limit (Fun.comp F L) = F^.obj (limit L)
:= rfl

/-! #brief A map out of the limit.
-/
theorem preslimit.out {X : Cat.{ℓobjx ℓhomx}} {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    (L : Fun X B) [L_HasLimit : HasLimit L]
    (F : Fun B C) [F_PresLimit : PresLimit L F]
    (x : X^.obj)
    : limit.out (Fun.comp F L) x = F^.hom (limit.out L x)
:= rfl

/-! #brief Every cone is mediated through the limit.
-/
definition preslimit.univ {X : Cat.{ℓobjx ℓhomx}} {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    (L : Fun X B) [L_HasLimit : HasLimit L]
    (F : Fun B C) [F_PresLimit : PresLimit L F]
    (c : Cone L)
    : limit.univ ((LeftConeFun F L)^.obj c) = by exact F^.hom (limit.univ c)
:= begin
     apply eq.symm,
     apply limit.univ.uniq ((LeftConeFun F L)^.obj c),
     intro x,
     dsimp [LeftConeFun],
     rw preslimit.out,
     refine eq.trans _ F^.hom_circ,
     rw limit.univ.mediates c x,
     trivial
   end



/- -----------------------------------------------------------------------
Final objects as limits.
----------------------------------------------------------------------- -/

/-! #brief If the initial functor has a limit, then the category has a final.
-/
instance InitFun.HasLimit_HasFinal {C : Cat.{ℓobj ℓhom}}
    [InitFun_HasLimit : HasLimit (InitFun.{ℓobjx ℓhomx} C)]
    : HasFinal C
:= let mkcone : C^.obj → Cone (InitFun.{ℓobjx ℓhomx} C)
             := λ c, { obj := c
                     , hom := λ e, by cases e
                     , comm := λ e₁ e₂ f, by cases f
                     }
   in HasFinal.show
       (limit (InitFun.{ℓobjx ℓhomx} C))
       (λ c, limit.univ (mkcone c))
       (λ c h, limit.univ.uniq (mkcone c) h (λ e, by cases e))

/-! #brief If the category has a final, then the initial functor has a limit.
-/
definition InitFun.HasFinal_HasLimit {C : Cat.{ℓobj ℓhom}}
    [HasFinal C]
    : HasLimit (InitFun.{ℓobjx ℓhomx} C)
:= HasLimit.show (final C) (λ e, by cases e) (λ x₁ x₂ f, by cases f)
    (λ c hom ωcomm, final_hom c)
    (λ c hom ωcomm e, by cases e)
    (λ c hom ωcomm f e, final_hom.uniq C)

/-! #brief Functors which preserve limits of the initial functor preserve final objects.
-/
instance PresLimit.InitFun_PresFinal {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    (F : Fun C D)
    [F_PresLimit : PresLimit (InitFun.{ℓobjx ℓhomx} C) F]
    : PresFinal F
:= let mk_cone : ∀ (d : D^.obj), Cone (F □□ InitFun.{ℓobjx ℓhomx} C)
              := λ d, { obj := d
                      , hom := λ e, by cases e
                      , comm := λ e₁ e₂ f, by cases f
                      } in
   let mk_lim : ∀ (C_HasFinal : HasFinal C)
                , HasLimit (F □□ InitFun.{ℓobjx ℓhomx} C)
             := λ C_HasFinal, @PresLimit.HasLimit _ _ _
                               _ (@InitFun.HasFinal_HasLimit C C_HasFinal)
                               _ F_PresLimit
   in { hom := λ C_HasFinal d, @limit.univ _ _ _ (mk_lim C_HasFinal) (mk_cone d)
      , pres := λ C_HasFinal
                , { hom_uniq := λ d h
                                , begin
                                    apply (@limit.univ.uniq _ _ _ (mk_lim C_HasFinal) (mk_cone d) h _),
                                    { intro e, cases e }
                                  end
                  }
      }



/- -----------------------------------------------------------------------
Co-limits.
----------------------------------------------------------------------- -/

/-! #brief A co-limit of a functor.
-/
@[class] definition HasCoLimit {X : Cat.{ℓobjx ℓhomx}} {C : Cat.{ℓobj₁ ℓhom₁}}
    (L : Fun X C)
:= HasLimit (OpFun L)

instance HasCoLimit.Op_HasLimit {X : Cat.{ℓobjx ℓhomx}} {C : Cat.{ℓobj₁ ℓhom₁}}
    (L : Fun X C)
    [L_HasCoLimit : HasCoLimit L]
    : HasLimit (OpFun L)
:= L_HasCoLimit

/-! #brief A category with all co-limits.
-/
class HasAllCoLimits (C : Cat.{ℓobj₁ ℓhom₁})
:= (has_colimit : ∀ {X : Cat.{ℓobjx ℓhomx}} (L : Fun X C)
                  , HasCoLimit L)

instance HasAllCoLimits.HasCoLimit {C : Cat.{ℓobj₁ ℓhom₁}}
    [C_HasAllCoLimits : HasAllCoLimits.{ℓobjx ℓhomx ℓobj₁ ℓhom₁} C]
    {X : Cat.{ℓobjx ℓhomx}} (L : Fun X C)
    : HasCoLimit L
:= HasAllCoLimits.has_colimit L

/-! #brief A category with all co-limits out of another category.
-/
class HasAllCoLimitsFrom (C : Cat.{ℓobj₁ ℓhom₁}) (X : Cat.{ℓobjx ℓhomx})
:= (has_colimit : ∀ (L : Fun X C), HasCoLimit L)

instance HasAllCoLimitsFrom.HasCoLimit (C : Cat.{ℓobj₁ ℓhom₁}) {X : Cat.{ℓobjx ℓhomx}}
    (L : Fun X C)
    [C_HasAllCoLimitsFrom_X : HasAllCoLimitsFrom C X]
    : HasCoLimit L
:= HasAllCoLimitsFrom.has_colimit L

/-! #brief Helper for showing a functor has a co-limit.
-/
definition HasCoLimit.show {X : Cat.{ℓobjx ℓhomx}} {C : Cat.{ℓobj₁ ℓhom₁}}
    {L : Fun X C}
    (l : C^.obj)
    (into : ∀ (x : X^.obj), C^.hom (L^.obj x) l)
    (ωinto : ∀ {x₁ x₂ : X^.obj} (f : X^.hom x₁ x₂)
             , into x₁ = C^.circ (into x₂) (L^.hom f))
    (univ
      : ∀ (c : C^.obj)
          (hom : ∀ (x : X^.obj), C^.hom (L^.obj x) c)
          (comm : ∀ {x₁ x₂ : X^.obj} (f : X^.hom x₁ x₂)
                  , hom x₁ = C^.circ (hom x₂) (L^.hom f))
        , C^.hom l c)
    (ωuniv
      : ∀ (c : C^.obj)
          (hom : ∀ (x : X^.obj), C^.hom (L^.obj x) c)
          (comm : ∀ {x₁ x₂ : X^.obj} (f : X^.hom x₁ x₂)
                  , hom x₁ = C^.circ (hom x₂) (L^.hom f))
          (x : X^.obj)
        , hom x = C^.circ (univ c hom @comm) (into x))
    (ωuniq
      : ∀ (c : C^.obj)
          (hom : ∀ (x : X^.obj), C^.hom (L^.obj x) c)
          (comm : ∀ {x₁ x₂ : X^.obj} (f : X^.hom x₁ x₂)
                  , hom x₁ = C^.circ (hom x₂) (L^.hom f))
          (f : C^.hom l c)
          (ωf : ∀ (x : X^.obj), hom x = C^.circ f (into x))
        , f = univ c hom @comm)
    : HasCoLimit L
:= HasLimit.show
    l into (λ x₂ x₁ f, ωinto f)
    (λ c hom comm, univ c hom (λ x₂ x₁ f, comm f))
    (λ c hom comm, ωuniv c hom (λ x₂ x₁ f, comm f))
    (λ c hom comm, ωuniq c hom (λ x₂ x₁ f, comm f))

/-! #brief Co-limits are co-cones.
-/
definition colimit.cocone {X : Cat.{ℓobjx ℓhomx}} {C : Cat.{ℓobj₁ ℓhom₁}}
    (F : Fun X C)
    [F_HasCoLimit : HasCoLimit F]
    : CoCone F
:= limit.cone (OpFun F)

/-! #brief The co-limit object of a functor.
-/
definition colimit {X : Cat.{ℓobjx ℓhomx}} {C : Cat.{ℓobj₁ ℓhom₁}}
    (F : Fun X C)
    [F_HasCoLimit : HasCoLimit F]
    : C^.obj
:= @limit (OpCat X) (OpCat C) (OpFun F) F_HasCoLimit

/-! #brief A map into the colimit.
-/
definition colimit.in {X : Cat.{ℓobjx ℓhomx}} {C : Cat.{ℓobj₁ ℓhom₁}}
    (F : Fun X C)
    [F_HasCoLimit : HasCoLimit F]
    (x : X^.obj)
    : C^.hom (F^.obj x) (colimit F)
:= limit.out (OpFun F) x

/-! #brief The co-limit-in maps commute with the diagram.
-/
theorem colimit.in.comm {X : Cat.{ℓobjx ℓhomx}} {C : Cat.{ℓobj₁ ℓhom₁}}
    (F : Fun X C)
    [F_HasCoLimit : HasCoLimit F]
    {x₁ x₂ : X^.obj}
    (f : X^.hom x₁ x₂)
    : colimit.in F x₁ = C^.circ (colimit.in F x₂) (F^.hom f)
:= limit.out.comm (OpFun F) f

/-! #brief Every co-cone is mediated through the co-limit.
-/
definition colimit.univ {X : Cat.{ℓobjx ℓhomx}} {C : Cat.{ℓobj₁ ℓhom₁}}
    {F : Fun X C}
    {F_HasCoLimit : HasCoLimit F}
    (c : CoCone F)
    : C^.hom (colimit F) c^.obj
:= limit.univ c

/-! #brief Every co-cone is mediated through the co-limit.
-/
theorem colimit.univ.mediates {X : Cat.{ℓobjx ℓhomx}} {C : Cat.{ℓobj₁ ℓhom₁}}
    {F : Fun X C}
    {F_HasCoLimit : HasCoLimit F}
    (c : CoCone F)
    (x : X^.obj)
    : c^.hom x = C^.circ (limit.univ c) (colimit.in F x)
:= limit.univ.mediates c x

/-! #brief The mediating map to a co-cone from the co-limit is unique.
-/
theorem colimit.univ.uniq {X : Cat.{ℓobjx ℓhomx}} {C : Cat.{ℓobj₁ ℓhom₁}}
    {F : Fun X C}
    {F_HasCoLimit : HasCoLimit F}
    (c : CoCone F)
    (m : C^.hom (colimit F) c^.obj)
    (ω : ∀ (x : X^.obj), c^.hom x = m ∘∘ colimit.in F x)
    : m = colimit.univ c
:= limit.univ.uniq c m ω

/-! #brief The unique iso between two co-limits of the same functor.
-/
definition colimit.iso {X : Cat.{ℓobjx ℓhomx}} {C : Cat.{ℓobj₁ ℓhom₁}}
    {F : Fun X C}
    (F_HasCoLimit₁ F_HasCoLimit₂ : HasCoLimit F)
    : C^.hom (@colimit X C F F_HasCoLimit₁) (@colimit X C F F_HasCoLimit₂)
:= limit.iso F_HasCoLimit₂ F_HasCoLimit₁

/-! #brief Co-limits are unique up-to unique isomorphism.
-/
theorem colimit.uniq {X : Cat.{ℓobjx ℓhomx}} {C : Cat.{ℓobj₁ ℓhom₁}}
    {F : Fun X C}
    (F_HasCoLimit₁ F_HasCoLimit₂ : HasCoLimit F)
    : Iso (limit.iso F_HasCoLimit₁ F_HasCoLimit₂)
          (limit.iso F_HasCoLimit₂ F_HasCoLimit₁)
:= limit.uniq F_HasCoLimit₁ F_HasCoLimit₂



/- -----------------------------------------------------------------------
Preservation of co-limits by functors.
----------------------------------------------------------------------- -/

/-! #brief A functor which preserves a co-limit.
-/
@[class] definition PresCoLimit {X : Cat.{ℓobjx ℓhomx}} {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    (L : Fun X B)
    (F : Fun B C)
:= PresLimit (OpFun L) (OpFun F)

instance PresCoLimit.PresLimit {X : Cat.{ℓobjx ℓhomx}} {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    (L : Fun X B)
    (F : Fun B C)
    [F_PresCoLimit : PresCoLimit L F]
    : PresLimit (OpFun L) (OpFun F)
:= F_PresCoLimit

/-! #brief Functors which preserve co-limits yield instances of HasCoLimit.
-/
instance PresCoLimit.HasCoLimit {X : Cat.{ℓobjx ℓhomx}} {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    (L : Fun X B) [L_HasCoLimit : HasCoLimit L]
    (F : Fun B C) [F_PresCoLimit : PresCoLimit L F]
    : HasCoLimit (Fun.comp F L)
:= PresLimit.HasLimit (OpFun L) (OpFun F)

/-! #brief A functor which preserves colimits out of a given category.
-/
class PresCoLimitsFrom {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    (F : Fun B C)
    (X : Cat.{ℓobjx ℓhomx})
:= (pres_colimit : ∀ (L : Fun X B)
                   , PresCoLimit L F)

instance PresCoLimitsFrom.PresCoLimit {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    (F : Fun B C)
    {X : Cat.{ℓobjx ℓhomx}}
    [F_PresCoLimitsFrom : PresCoLimitsFrom F X]
    (L : Fun X B)
    : PresCoLimit L F
:= PresCoLimitsFrom.pres_colimit F L

/-! #brief Helper for showing that a functor preserves a co-limit.
-/
definition PresCoLimit.show {X : Cat.{ℓobjx ℓhomx}} {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    {L : Fun X B}
    {F : Fun B C}
    (mediate
      : ∀ [L_HasCoLimit : HasCoLimit L]
          (c : C^.obj)
          (hom : ∀ (x : X^.obj), C^.hom (F^.obj (L^.obj x)) c)
          (ωcomm : ∀ {x₁ x₂ : X^.obj} (f : X^.hom x₁ x₂)
                   , hom x₁ = C^.circ (hom x₂) (F^.hom (L^.hom f)))
        , C^.hom (F^.obj (colimit L)) c)
    (ωmediate
      : ∀ [L_HasCoLimit : HasCoLimit L]
          (c : C^.obj)
          (hom : ∀ (x : X^.obj), C^.hom (F^.obj (L^.obj x)) c)
          (ωcomm : ∀ {x₁ x₂ : X^.obj} (f : X^.hom x₁ x₂)
                   , hom x₁ = C^.circ (hom x₂) (F^.hom (L^.hom f)))
          (x : X^.obj)
        , hom x = mediate c hom @ωcomm ∘∘ F^.hom (colimit.in L x))
    (ωuniq
      : ∀ [L_HasCoLimit : HasCoLimit L]
          (c : C^.obj)
          (hom : ∀ (x : X^.obj), C^.hom (F^.obj (L^.obj x)) c)
          (ωcomm : ∀ {x₁ x₂ : X^.obj} (f : X^.hom x₁ x₂)
                   , hom x₁ = C^.circ (hom x₂) (F^.hom (L^.hom f)))
          (f : C^.hom (F^.obj (colimit L)) c)
          (ωf : ∀ (x : X^.obj), hom x = C^.circ f (F^.hom (colimit.in L x)))
        , f = mediate c hom @ωcomm)
    : PresCoLimit L F
:= PresLimit.show
    (λ L_HasCoLimit c hom ωcomm, @mediate L_HasCoLimit c hom (λ x₂ x₁ f, ωcomm f))
    (λ L_HasCoLimit c hom ωcomm, @ωmediate L_HasCoLimit c hom (λ x₂ x₁ f, ωcomm f))
    (λ L_HasCoLimit c hom ωcomm, @ωuniq L_HasCoLimit c hom (λ x₂ x₁ f, ωcomm f))

/-! #brief A co-limit of a functor.
-/
theorem prescolimit {X : Cat.{ℓobjx ℓhomx}} {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    (L : Fun X B) [L_HasCoLimit : HasCoLimit L]
    (F : Fun B C) [F_PresCoLimit : PresCoLimit L F]
    : colimit (Fun.comp F L) = F^.obj (colimit L)
:= preslimit (OpFun L) (OpFun F)

/-! #brief A map into the co-limit.
-/
theorem prescolimit.in {X : Cat.{ℓobjx ℓhomx}} {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    (L : Fun X B) [L_HasCoLimit : HasCoLimit L]
    (F : Fun B C) [F_PresCoLimit : PresCoLimit L F]
    (x : X^.obj)
    : colimit.in (Fun.comp F L) x = F^.hom (colimit.in L x)
:= preslimit.out (OpFun L) (OpFun F) x

/-! #brief Every co-cone is mediated through the co-limit.
-/
definition prescolimit.mediate {X : Cat.{ℓobjx ℓhomx}} {B : Cat.{ℓobj₁ ℓhom₁}} {C : Cat.{ℓobj₂ ℓhom₂}}
    (L : Fun X B) [L_HasCoLimit : HasCoLimit L]
    (F : Fun B C) [F_PresCoLimit : PresCoLimit L F]
    (c : CoCone L)
    : colimit.univ ((LeftCoConeFun F L)^.obj c) = by exact F^.hom (colimit.univ c)
:= preslimit.univ (OpFun L) (OpFun F) c



/- -----------------------------------------------------------------------
Initial objects as co-limits.
----------------------------------------------------------------------- -/

/-! #brief If the initial functor has a co-limit, then the category has a final.
-/
instance InitFun.HasCoLimit_HasInit {C : Cat.{ℓobj ℓhom}}
    [InitFun_HasCoLimit : HasCoLimit (InitFun.{ℓobjx ℓhomx} C)]
    : HasInit C
:= let mkcone : C^.obj → CoCone (InitFun.{ℓobjx ℓhomx} C)
             := λ c, { obj := c
                     , hom := λ e, by cases e
                     , comm := λ e₁ e₂ f, by cases f
                     }
   in HasInit.show
       (colimit (InitFun.{ℓobjx ℓhomx} C))
       (λ c, colimit.univ (mkcone c))
       (λ c h, limit.univ.uniq (mkcone c) h (λ e, by cases e))

/-! #brief If the category has an initial, then the initial functor has a co-limit.
-/
definition InitFun.HasInit_HasCoLimit {C : Cat.{ℓobj ℓhom}}
    [HasInit C]
    : HasCoLimit (InitFun.{ℓobjx ℓhomx} C)
:= HasCoLimit.show (init C) (λ e, by cases e) (λ x₁ x₂ f, by cases f)
    (λ c hom ωcomm, init_hom c)
    (λ c hom ωcomm e, by cases e)
    (λ c hom ωcomm f e, init_hom.uniq C)

/-! #brief Functors which preserve co-limits of the initial functor preserve initial objects.
-/
instance PresCoLimit.InitFun_PresInit {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    (F : Fun C D)
    [F_PresCoLimit : PresCoLimit (InitFun.{ℓobjx ℓhomx} C) F]
    : PresInit F
:= let mk_cocone : ∀ (d : D^.obj), CoCone (F □□ InitFun.{ℓobjx ℓhomx} C)
                := λ d, { obj := d
                        , hom := λ e, by cases e
                        , comm := λ e₁ e₂ f, by cases f
                        } in
   let mk_colim : ∀ (C_HasInit : HasInit C)
                  , HasCoLimit (F □□ InitFun.{ℓobjx ℓhomx} C)
               := λ C_HasInit, @PresCoLimit.HasCoLimit _ _ _
                                 _ (@InitFun.HasInit_HasCoLimit C C_HasInit)
                                 _ F_PresCoLimit
   in { hom := λ C_HasInit d, @colimit.univ _ _ _ (mk_colim C_HasInit) (mk_cocone d)
      , pres := λ C_HasInit
                , { hom_uniq := λ d h
                                , begin
                                    apply (@colimit.univ.uniq _ _ _ (mk_colim C_HasInit) (mk_cocone d) h _),
                                    { intro e, cases e }
                                  end
                  }
      }



/- -----------------------------------------------------------------------
Limits and adjoints.
----------------------------------------------------------------------- -/

/-! #brief Right adjoints preserve all limits.
-/
definition Adj.right.PresLimit
    {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {L : Fun C D} {R : Fun D C}
    (adj : Adj L R)
    {X : Cat.{ℓobjx ℓhomx}} (F : Fun X D)
    : PresLimit F R
:= PresLimit.show
     (λ F_HasLimit c hom ω
      , adj^.right_adj
         (@limit.univ _ _ F F_HasLimit
           { obj := L^.obj c
           , hom := λ x, adj^.left_adj (hom x)
           , comm := λ x₁ x₂ f, begin rw ω f, exact sorry end
           }))
     (λ F_HasLimit c hom ωcomm x, sorry)
     (λ F_HasLimit c hom ωcomm h ω, sorry)

/-! #brief Left adjoints preserve all co-limits.
-/
definition Adj.left.PresCoLimit
    {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    {L : Fun C D} {R : Fun D C}
    (adj : Adj L R)
    {X : Cat.{ℓobjx ℓhomx}} (F : Fun X C)
    : PresCoLimit F L
:= PresCoLimit.show
     (λ F_HasLimit c hom ω
      , adj^.left_adj
         (@colimit.univ _ _ F F_HasLimit
           { obj := R^.obj c
           , hom := λ x, adj^.right_adj (hom x)
           , comm := λ x₁ x₂ f, begin rw ω f, exact sorry end
           }))
     (λ F_HasLimit c hom ωcomm x, sorry)
     (λ F_HasLimit c hom ωcomm h ω, sorry)


end qp
