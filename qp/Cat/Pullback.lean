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
@[reducible] definition Pullback.show_cone {C : Cat.{ℓobj ℓhom}}
    {a b z : [[C]]}
    (ga : a →→ z) (gb : b →→ z)
    (pb : [[C]])
    (π₁ : pb →→ a) (π₂ : pb →→ b)
    (ωtriangle : ga ∘∘ π₁ = gb ∘∘ π₂)
    : Cone (CoSpanDrgm ga gb)
:= { obj := pb
   , proj := λ x, CoSpanCat.Obj.cases_on x π₁ π₂ (ga ∘∘ π₁)
   , triangle := λ x₁ x₂ f, begin cases f, { simp }, { simp }, { exact ωtriangle } end
   }

/-! #brief Helper for building a pullback.
-/
@[reducible] definition Pullback.show {C : Cat.{ℓobj ℓhom}}
    {a b z : [[C]]}
    (ga : a →→ z) (gb : b →→ z)
    (pb : [[C]])
    (π₁ : pb →→ a) (π₂ : pb →→ b)
    (mediate : ∀ (cone : Cone (CoSpanDrgm ga gb)), C^.hom cone pb)
    (ωtriangle : ga ∘∘ π₁ = gb ∘∘ π₂)
    (ωcone_a : ∀ (cone : Cone (CoSpanDrgm ga gb)), cone^.proj CoSpanCat.Obj.a = π₁ ∘∘ mediate cone)
    (ωcone_b : ∀ (cone : Cone (CoSpanDrgm ga gb)), cone^.proj CoSpanCat.Obj.b = π₂ ∘∘ mediate cone)
    (ωuniq : ∀ (cone : Cone (CoSpanDrgm ga gb)) (h : ConeHom cone (Pullback.show_cone ga gb pb π₁ π₂ ωtriangle)), h^.mediate = mediate cone)
    : Pullback ga gb
:= Limit.show (CoSpanDrgm ga gb) pb
    (λ x, CoSpanCat.Obj.cases_on x π₁ π₂ (ga ∘∘ π₁))
    mediate
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
:= Limit.mediate pb (Pullback.show_cone ga gb c fa fb ωsquare)

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



/- ----------------------------------------------------------------------------
Categories with pullbacks.
---------------------------------------------------------------------------- -/

/-! #brief A category with all pullbacks.
-/
@[reducible] definition HasAllPullbacks (C : Cat.{ℓobj ℓhom})
    : Type (max 1 ℓobj ℓhom)
:= ∀ {a b z : [[C]]} (ga : a →→ z) (gb : b →→ z)
   , Pullback ga gb

/-! #brief Categories with all limits have all pullbacks.
-/
@[reducible] definition HasAllLimits.HasAllPullbacks {C : Cat.{ℓobj ℓhom}}
    (C_HasAllLimits : HasAllLimits C)
    : HasAllPullbacks C
:= λ a b z ga gb, C_HasAllLimits (CoSpanDrgm ga gb)

/-! #brief A category with all pullbacks along a given hom.
-/
@[reducible] definition HasAllPullbacksAlong (C : Cat.{ℓobj ℓhom})
    {a z : [[C]]} (ga : a →→ z)
    : Type (max 1 ℓobj ℓhom)
:= ∀ {b : [[C]]} (gb : b →→ z)
   , Pullback ga gb

/-! #brief A category with all pullbacks has all pullbacks along every hom.
-/
@[reducible] definition HasAllPullbacks.HasAllPullbacksAlong {C : Cat.{ℓobj ℓhom}}
    (C_HasAllPullbacks : HasAllPullbacks C)
    {a z : [[C]]} (ga : a →→ z)
    : HasAllPullbacksAlong C ga
:= λ b gb, C_HasAllPullbacks ga gb



/- ----------------------------------------------------------------------------
The base change functor.
---------------------------------------------------------------------------- -/

/-! #brief Base change functor.
-/
@[reducible] definition BaseChangeFun {C : Cat.{ℓobj ℓhom}}
    {c₁ c₂ : [[C]]} {base : c₁ →→ c₂}
    (base_HasPullbacksAlong : HasAllPullbacksAlong C base)
    : SliceCat C c₂ ⇉⇉ SliceCat C c₁
:= { obj := λ x, { dom := base_HasPullbacksAlong x^.hom
                 , hom := Pullback.π₁ (base_HasPullbacksAlong x^.hom)
                 }
   , hom := λ x y f, { hom := Pullback.into (base_HasPullbacksAlong y^.hom)
                               (Pullback.π₁ (base_HasPullbacksAlong x^.hom))
                               (f^.hom ∘∘ Pullback.π₂ (base_HasPullbacksAlong x^.hom))
                               begin exact sorry end
                     , triangle := begin exact sorry end
                     }
   , hom_id := λ x, begin apply SliceCat.Hom.eq, exact sorry end
   , hom_circ := λ x y z g f, begin apply SliceCat.Hom.eq, exact sorry end
   }

end qp
