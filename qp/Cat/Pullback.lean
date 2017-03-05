/- ----------------------------------------------------------------------------
Pullbacks.
---------------------------------------------------------------------------- -/

import .basic
import .Cone

namespace qp
universe variables ℓobj ℓhom



/- ----------------------------------------------------------------------------
The co-span category.
---------------------------------------------------------------------------- -/

/-! #brief An object in CoSpanCat.
-/
inductive CoSpanCat.Obj : Type | a | b | z

/-! #brief A hom in CoSpanCat.
-/
inductive CoSpanCat.Hom : CoSpanCat.Obj → CoSpanCat.Obj → Type
| id : ∀ (s : CoSpanCat.Obj), CoSpanCat.Hom s s
| a : CoSpanCat.Hom CoSpanCat.Obj.a CoSpanCat.Obj.z
| b : CoSpanCat.Hom CoSpanCat.Obj.b CoSpanCat.Obj.z

/-! #brief Composition of homs in CoSpanCat.
-/
@[reducible] definition CoSpanCat.Hom.comp
    : ∀ {m n p : CoSpanCat.Obj}
        (g : CoSpanCat.Hom n p)
        (f : CoSpanCat.Hom m n)
      , CoSpanCat.Hom m p
| m n p g f
:= begin
     cases f,
     { exact g },
     { 
       cases g,
       { exact CoSpanCat.Hom.a },
     },
     { cases g,
       { exact CoSpanCat.Hom.b },
     }
   end

/-! #brief The co-span category.
-/
@[reducible] definition CoSpanCat : Cat
:= { obj := CoSpanCat.Obj
   , hom := CoSpanCat.Hom
   , id := CoSpanCat.Hom.id
   , circ := @CoSpanCat.Hom.comp
   , circ_assoc
      := λ m n p q h g f
         , begin
             cases f,
             { apply rfl },
             { cases g, apply rfl },
             { cases g, apply rfl }
           end
   , circ_id_left := λ m n f, begin cases f, apply rfl, apply rfl, apply rfl end
   , circ_id_right := λ m n f, rfl
   }

/-! #brief Construct a cospan diagram.
-/
@[reducible] definition CoSpanDrgm {C : Cat.{ℓobj ℓhom}}
    {a b z : [[C]]}
    (fa : a →→ z) (fb : b →→ z)
    : CoSpanCat ⇉⇉ C
:= { obj := λ m, CoSpanCat.Obj.cases_on m a b z
   , hom := λ m n f, begin cases f, apply C^.id, exact fa, exact fb end
   , hom_id := λ m, rfl
   , hom_circ
      := λ m n p g f
         , begin
             cases f,
             { rw CoSpanCat^.circ_id_right, dsimp, rw C^.circ_id_right },
             { cases g, rw CoSpanCat^.circ_id_left, dsimp, rw C^.circ_id_left },
             { cases g, rw CoSpanCat^.circ_id_left, dsimp, rw C^.circ_id_left }
           end
   }

/-! #brief Action of CoSpanDrgm on CoSpanCat.Hom.a.
-/
@[simp] theorem CoSpanDrgm.hom_a {C : Cat.{ℓobj ℓhom}}
    {a b z : [[C]]}
    (fa : a →→ z) (fb : b →→ z)
    : (CoSpanDrgm fa fb)^.hom CoSpanCat.Hom.a = fa
:= rfl

/-! #brief Action of CoSpanDrgm on CoSpanCat.Hom.b.
-/
@[simp] theorem CoSpanDrgm.hom_b {C : Cat.{ℓobj ℓhom}}
    {a b z : [[C]]}
    (fa : a →→ z) (fb : b →→ z)
    : (CoSpanDrgm fa fb)^.hom CoSpanCat.Hom.b = fb
:= rfl



/- ----------------------------------------------------------------------------
Pullbacks.
---------------------------------------------------------------------------- -/

/-! #brief A pullback is a limit of a cospan diagram.
-/
@[reducible] definition Pullback {C : Cat.{ℓobj ℓhom}}
    {a b z : [[C]]}
    (ga : a →→ z) (gb : b →→ z)
    : Type (max 1 ℓobj ℓhom)
:= Limit (CoSpanDrgm ga gb)

/-! #brief Helper for the helper for building a pullback.
-/
@[reducible] definition Pullback.mk_cone {C : Cat.{ℓobj ℓhom}}
    {a b z : [[C]]}
    (ga : a →→ z) (gb : b →→ z)
    (pb : [[C]])
    (π₁ : pb →→ a) (π₂ : pb →→ b)
    (ωtriangle : ga ∘∘ π₁ = gb ∘∘ π₂)
    : Cone (CoSpanDrgm ga gb)
:= { obj := pb
   , hom := λ x, CoSpanCat.Obj.cases_on x π₁ π₂ (ga ∘∘ π₁)
   , triangle := λ x₁ x₂ f, begin cases f, { simp }, { simp }, { exact ωtriangle } end
   }

/-! #brief Helper for building a pullback.
-/
@[reducible] definition Pullback.mk {C : Cat.{ℓobj ℓhom}}
    {a b z : [[C]]}
    (ga : a →→ z) (gb : b →→ z)
    (pb : [[C]])
    (π₁ : pb →→ a) (π₂ : pb →→ b)
    (into : ∀ (cone : Cone (CoSpanDrgm ga gb)), C^.hom cone pb)
    (ωtriangle : ga ∘∘ π₁ = gb ∘∘ π₂)
    (ωcone_a : ∀ (cone : Cone (CoSpanDrgm ga gb)), cone^.hom CoSpanCat.Obj.a = π₁ ∘∘ into cone)
    (ωcone_b : ∀ (cone : Cone (CoSpanDrgm ga gb)), cone^.hom CoSpanCat.Obj.b = π₂ ∘∘ into cone)
    (ωuniq : ∀ (cone : Cone (CoSpanDrgm ga gb)) (h : ConeHom cone (Pullback.mk_cone ga gb pb π₁ π₂ ωtriangle)), h^.mediate = into cone)
    : Pullback ga gb
:= Limit.mk (CoSpanDrgm ga gb) pb
    (λ x, CoSpanCat.Obj.cases_on x π₁ π₂ (ga ∘∘ π₁))
    into
    (λ x₁ x₂ f, begin cases f, { simp }, { simp }, { exact ωtriangle } end)
    (λ cone x, begin cases x, { apply ωcone_a }, { apply ωcone_b }, { dsimp, rw cone^.triangle Hom.a, dsimp, rw [ωcone_a, C^.circ_assoc] } end)
    ωuniq

/-! #brief Homs into a pullback.
-/
@[reducible] definition Pullback.into {C : Cat.{ℓobj ℓhom}}
    {a b z : [[C]]}
    {ga : a →→ z} {gb : b →→ z}
    (pb : Pullback ga gb)
    {c : [[C]]}
    (fa : c →→ a) (fb : c →→ b)
    (ωsquare : ga ∘∘ fa = gb ∘∘ fb)
    : C^.hom c pb
:= Limit.univ pb (Pullback.mk_cone ga gb c fa fb ωsquare)

/-! #brief Projection from a pullback.
-/
@[reducible] definition Pullback.π₁ {C : Cat.{ℓobj ℓhom}}
    {a b z : [[C]]}
    {ga : a →→ z} {gb : b →→ z}
    (pb : Pullback ga gb)
    : C^.hom pb a
:= pb^.proj CoSpanCat.Obj.a

/-! #brief Projection from a pullback.
-/
@[reducible] definition Pullback.π₂ {C : Cat.{ℓobj ℓhom}}
    {a b z : [[C]]}
    {ga : a →→ z} {gb : b →→ z}
    (pb : Pullback ga gb)
    : C^.hom pb b
:= pb^.proj CoSpanCat.Obj.b

-- TODO:
-- Pullback.into.factor
-- Pullback.into.uniq
-- ga ∘∘ Pullback.π₁ = gb ∘∘ Pullback.π₂



/- ----------------------------------------------------------------------------
Categories with pullbacks.
---------------------------------------------------------------------------- -/

/-! #brief A category with all pullbacks along a given hom.
-/
class HasAllPullbacksAlong (C : Cat.{ℓobj ℓhom})
    {a z : [[C]]} (ga : a →→ z)
    : Type (max 1 ℓobj ℓhom)
:= { pullback : ∀ {b : [[C]]} (gb : b →→ z)
                , Pullback ga gb
   }

/-! #brief A category with all pullbacks.
-/
class HasAllPullbacks (C : Cat.{ℓobj ℓhom})
    : Type (max 1 ℓobj ℓhom)
:= { pullback : ∀ {a b z : [[C]]} (ga : a →→ z) (gb : b →→ z)
                , Pullback ga gb
   }

/-! #brief The pullback of two homs.
-/
definition pullback {C : Cat.{ℓobj ℓhom}}
    [C_HasAllPullbacks : HasAllPullbacks C]
    {a b z : [[C]]} (ga : a →→ z) (gb : b →→ z)
    : Pullback ga gb
:= HasAllPullbacks.pullback ga gb

/-! #brief Categories with all limits have all pullbacks.
-/
instance HasAllLimits.HasAllPullbacks {C : Cat.{ℓobj ℓhom}}
    [C_HasAllLimits : HasAllLimits C]
    : HasAllPullbacks C
:= @HasAllPullbacks.mk C (λ a b z ga gb, limit (CoSpanDrgm ga gb))

/-! #brief The pullback along a hom.
-/
definition pullback_along {C : Cat.{ℓobj ℓhom}}
    {a z : [[C]]} (base : a →→ z)
    [base_HasPullbacksAlong : HasAllPullbacksAlong C base]
    {b : [[C]]} (f : b →→ z)
    : Pullback base f
:= HasAllPullbacksAlong.pullback base f

/-! #brief A category with all pullbacks has all pullbacks along every hom.
-/
instance HasAllPullbacks.HasAllPullbacksAlong {C : Cat.{ℓobj ℓhom}}
    [C_HasAllPullbacks : HasAllPullbacks C]
    {a z : [[C]]} (ga : a →→ z)
    : HasAllPullbacksAlong C ga
:= @HasAllPullbacksAlong.mk C a z ga (λ b gb, pullback ga gb)



/- ----------------------------------------------------------------------------
The base change functor.
---------------------------------------------------------------------------- -/

/-! #brief Base change functor.
-/
@[reducible] definition BaseChangeFun {C : Cat.{ℓobj ℓhom}}
    {c₁ c₂ : [[C]]}
    (base : c₁ →→ c₂)
    [base_HasPullbacksAlong : HasAllPullbacksAlong C base]
    : SliceCat C c₂ ⇉⇉ SliceCat C c₁
:= { obj := λ x, { dom := pullback_along base x^.hom
                 , hom := Pullback.π₁ (pullback_along base x^.hom)
                 }
   , hom := λ x y f, { hom := Pullback.into (pullback_along base y^.hom)
                               (Pullback.π₁ (pullback_along base x^.hom))
                               (f^.hom ∘∘ Pullback.π₂ (pullback_along base x^.hom))
                               begin exact sorry end
                     , triangle := begin exact sorry end
                     }
   , hom_id := λ x, begin apply SliceHom.eq, exact sorry end
   , hom_circ := λ x y z g f, begin apply SliceHom.eq, exact sorry end
   }

end qp
