/- ----------------------------------------------------------------------------
Pullbacks.
---------------------------------------------------------------------------- -/

import .basic
import .Cone
import ..Qvr.basic
import ..Qvr.FreeCat
import ..Qvr.FreeFrgtAdj
import ..util

namespace qp
universe variables ℓobj ℓhom



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

/-! #brief Helper for defining pullback diagrams.
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

-- A pullback is a limit of a cospan diagram.
structure IsPullback {C : Cat.{ℓobj ℓhom}}
    {a b z : [[C]]}
    (ga : a →→ z) (gb : b →→ z)
    {x : [[C]]}
    (fa : x →→ a) (fb : x →→ b)
    : Type (max 1 ℓobj ℓhom)
:= (is_limit : IsLimit (CoSpanDrgm ga gb) x)
   (proj_a : is_limit^.proj CoSpanCat.Obj.a = fa)
   (proj_b : is_limit^.proj CoSpanCat.Obj.b = fb)

-- TODO: Fix docstring!
--/-! #brief A helper for the helper for proving one has a pullback square.
---/
@[reducible] definition IsPullback.show_cone {C : Cat.{ℓobj ℓhom}}
    {a b z : [[C]]}
    (ga : a →→ z) (gb : b →→ z)
    {x : [[C]]}
    (fa : x →→ a) (fb : x →→ b)
    (ωsquare : ga ∘∘ fa = gb ∘∘ fb)
    (mediate : ∀ (cone : [[ConeCat (CoSpanDrgm ga gb)]]), cone^.cone →→ x)
    : IsCone (CoSpanDrgm ga gb) x
:= { proj := λ m, CoSpanCat.Obj.cases_on m fa fb (ga ∘∘ fa)
   , triangle
      := λ m n f
         , begin
             cases f,
             { simp },
             { simp },
             { exact ωsquare }
             end
   }

/-! #brief A helper to prove one has a pullback square.
-/
@[reducible] definition IsPullback.show {C : Cat.{ℓobj ℓhom}}
    {a b z : [[C]]}
    (ga : a →→ z) (gb : b →→ z)
    {x : [[C]]}
    (fa : x →→ a) (fb : x →→ b)
    (mediate : ∀ (cone : [[ConeCat (CoSpanDrgm ga gb)]]), cone^.cone →→ x)
    (ωsquare : ga ∘∘ fa = gb ∘∘ fb)
    (ωfactor_a : ∀ (cone : [[ConeCat (CoSpanDrgm ga gb)]])
                 , cone^.is_cone^.proj CoSpanCat.Obj.a
                    = fa ∘∘ mediate cone)
    (ωfactor_b : ∀ (cone : [[ConeCat (CoSpanDrgm ga gb)]])
                 , cone^.is_cone^.proj CoSpanCat.Obj.b
                    = fb ∘∘ mediate cone)
    (ωuniq : ∀ (cone : [[ConeCat (CoSpanDrgm ga gb)]])
               (h : (ConeCat (CoSpanDrgm ga gb))^.hom
                     cone
                     (BxCone.mk x (IsPullback.show_cone ga gb fa fb ωsquare mediate)))
             , h^.mediate = mediate cone)
    : IsPullback ga gb fa fb
:= { is_limit
      := { is_cone := IsPullback.show_cone ga gb fa fb ωsquare mediate
         , is_final
            := { final
                  := λ cone
                     , { mediate := mediate cone
                       , factor
                          := λ s
                             , begin
                                 cases s,
                                 { apply ωfactor_a },
                                 { apply ωfactor_b },
                                 simp, rw cone^.is_cone^.triangle CoSpanCat.Hom.a,
                                 dsimp, rw ωfactor_a, rw Cat.circ_assoc
                               end
                       }
               , uniq := λ cone h, begin apply ConeHom.eq, apply ωuniq end
               }
         }
   , proj_a := rfl
   , proj_b := rfl
   }

end qp
