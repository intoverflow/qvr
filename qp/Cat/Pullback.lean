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


-- /-! #brief The vertices of the cospan quiver.
-- -/
-- inductive CoSpan : Type
-- | a | b | z

-- /-! #brief The arrows of the cospan quiver.
-- -/
-- inductive CoSpan.Arr : Type
-- | a | b

-- /-! #brief The source of a vertex in the cospan quiver.
-- -/
-- @[reducible] definition CoSpan.Arr.src : CoSpan.Arr → CoSpan
-- | CoSpan.Arr.a := CoSpan.a
-- | CoSpan.Arr.b := CoSpan.b

-- /-! #brief The cospan quiver.
-- -/
-- @[reducible] definition CoSpanQvr
--     : Qvr.{1 1}
-- := { vtx := CoSpan
--    , arr := CoSpan.Arr
--    , src := CoSpan.Arr.src
--    , dst := λ e, CoSpan.z
--    }

-- /-! #brief The cospan category.
-- -/
-- @[reducible] definition CoSpanCat
--     : Cat.{1 1}
-- := FreeCat CoSpanQvr

-- /-! #brief Walking structure of CoSpanCat.
-- -/
-- theorem CoSpanCat.walk_a_a
--     : ∀ (f : CoSpanCat^.hom CoSpan.a CoSpan.a)
--       , f = FreeCat.Hom.id CoSpan.a
-- := sorry

-- /-! #brief Walking structure of CoSpanCat.
-- -/
-- definition {ℓ} CoSpanCat.walk_a_b {T : Type ℓ}
--     : ∀ (f : CoSpanCat^.hom CoSpan.a CoSpan.b)
--       , T
-- := sorry

-- /-! #brief Walking structure of CoSpanCat.
-- -/
-- theorem CoSpanCat.walk_a_z
--     : ∀ (f : CoSpanCat^.hom CoSpan.a CoSpan.z)
--       , f = (@FreeCat.Hom.step CoSpanQvr _ _ _ ⌊CoSpan.Arr.a⌋ (FreeCat.Hom.id _))
-- := sorry

-- /-! #brief Walking structure of CoSpanCat.
-- -/
-- theorem {ℓ} CoSpanCat.walk_b_a {T : Type ℓ}
--     : ∀ (f : CoSpanCat^.hom CoSpan.b CoSpan.a)
--       , T
-- := sorry

-- /-! #brief Walking structure of CoSpanCat.
-- -/
-- definition CoSpanCat.walk_b_b
--     : ∀ (f : CoSpanCat^.hom CoSpan.b CoSpan.b)
--       , f = FreeCat.Hom.id CoSpan.b
-- := sorry

-- /-! #brief Walking structure of CoSpanCat.
-- -/
-- theorem CoSpanCat.walk_b_z
--     : ∀ (f : CoSpanCat^.hom CoSpan.b CoSpan.z)
--       , f = (@FreeCat.Hom.step CoSpanQvr _ _ _ ⌊CoSpan.Arr.b⌋ (FreeCat.Hom.id _))
-- := sorry

-- /-! #brief Walking structure of CoSpanCat.
-- -/
-- theorem {ℓ} CoSpanCat.walk_z_a {T : Type ℓ}
--     : ∀ (f : CoSpanCat^.hom CoSpan.z CoSpan.a)
--       , T
-- := sorry

-- /-! #brief Walking structure of CoSpanCat.
-- -/
-- theorem {ℓ} CoSpanCat.walk_z_b {T : Type ℓ}
--     : ∀ (f : CoSpanCat^.hom CoSpan.z CoSpan.b)
--       , T
-- := sorry

-- /-! #brief Walking structure of CoSpanCat.
-- -/
-- theorem CoSpanCat.walk_z_z
--     : ∀ (f : CoSpanCat^.hom CoSpan.z CoSpan.z)
--       , f = FreeCat.Hom.id CoSpan.z
-- := sorry

-- /-! #brief Structure theorem for homs in CoSpanCat.
-- -/
-- theorem {ℓ} CoSpanCat.cases_hom (P : ∀ {x₁ x₂ : [[CoSpanCat]]} (f : CoSpanCat^.hom x₁ x₂), Prop)
--     (ωa : P (FreeCat.Hom.id CoSpan.a))
--     (ωb : P (FreeCat.Hom.id CoSpan.b))
--     (ωz : P (FreeCat.Hom.id CoSpan.z))
--     (ωfa : P (FreeCat.Hom.step _ _ _ ⌊CoSpan.Arr.a⌋ (FreeCat.Hom.id _)))
--     (ωfb : P (FreeCat.Hom.step _ _ _ ⌊CoSpan.Arr.b⌋ (FreeCat.Hom.id _)))
--     : ∀ {x₁ x₂ : [[CoSpanCat]]} (f : CoSpanCat^.hom x₁ x₂), P f
-- | CoSpan.a CoSpan.a f := begin rw CoSpanCat.walk_a_a f, apply ωa end
-- | CoSpan.a CoSpan.b f := begin apply CoSpanCat.walk_a_b f end
-- | CoSpan.a CoSpan.z f := begin rw CoSpanCat.walk_a_z f, apply ωfa end
-- | CoSpan.b CoSpan.a f := begin apply CoSpanCat.walk_b_a f end
-- | CoSpan.b CoSpan.b f := begin rw CoSpanCat.walk_b_b f, apply ωb end
-- | CoSpan.b CoSpan.z f := begin rw CoSpanCat.walk_b_z f, apply ωfb end
-- | CoSpan.z CoSpan.a f := begin apply CoSpanCat.walk_z_a f end
-- | CoSpan.z CoSpan.b f := begin apply CoSpanCat.walk_z_b f end
-- | CoSpan.z CoSpan.z f := begin rw CoSpanCat.walk_z_z f, apply ωz end

-- /-! #brief Helper for defining pullback diagrams.
-- -/
-- @[reducible] definition PullbackFun {C : Cat.{ℓobj ℓhom}}
--     {a b z : [[C]]}
--     (fa : a →→ z) (fb : b →→ z)
--     : CoSpanCat ⇉⇉ C
-- := FreeCat_FrgtQvr_Adj.free_adjoint
--     { vtx := λ x, CoSpan.cases_on x a b z
--     , arr := λ e, CoSpan.Arr.cases_on e (Cat.BxHom.mk _ _ fa) (Cat.BxHom.mk _ _ fb)
--     , src := λ e, begin cases e, { apply rfl }, { apply rfl } end
--     , dst := λ e, begin cases e, { apply rfl }, { apply rfl } end
--     }

-- -- A pullback is a limit of a cospan diagram.
-- structure IsPullback {C : Cat.{ℓobj ℓhom}}
--     {a b z : [[C]]}
--     (fa : a →→ z) (fb : b →→ z)
--     {x : [[C]]}
--     (ga : x →→ a) (gb : x →→ b)
--     : Type (max 1 ℓobj ℓhom)
-- := (is_limit : IsLimit (PullbackFun fa fb) x)
--    (proj_a : is_limit^.proj CoSpan.a = ga)
--    (proj_b : is_limit^.proj CoSpan.b = gb)

-- -- TODO: Fix docstring!
-- --/-! #brief Every limit of PullbackFun is a pullback.
-- ---/
-- @[reducible] definition PullbackFun.limit_is_pullback {C : Cat.{ℓobj ℓhom}}
--     {a b z : [[C]]}
--     (fa : a →→ z) (fb : b →→ z)
--     {x : [[C]]}
--     (x_limit : IsLimit (PullbackFun fa fb) x)
--     : IsPullback fa fb (x_limit^.proj CoSpan.a) (x_limit^.proj CoSpan.b)
-- := { is_limit := x_limit
--    , proj_a := rfl
--    , proj_b := rfl
--    }

end qp
