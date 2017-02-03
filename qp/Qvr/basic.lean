/- ----------------------------------------------------------------------------
Quivers.
---------------------------------------------------------------------------- -/

import ..Cat.basic

namespace qp
universe variables ℓvtx ℓarr ℓvtx₁ ℓarr₁ ℓvtx₂ ℓarr₂ ℓvtx₃ ℓarr₃ ℓvtx₄ ℓarr₄



/- ----------------------------------------------------------------------------
A quiver is a "bag of arrows:" a directed (multi)graph. A quiver morphism is
just a morphism of directed graphs.
---------------------------------------------------------------------------- -/

-- A quiver.
structure Qvr : Type ((max ℓvtx ℓarr) + 1)
:= (vtx : Type.{ℓvtx})
   (arr : Type.{ℓarr})
   (src : arr → vtx)
   (dst : arr → vtx)

-- A vertex in a quiver.
-- \Vert \Vert
notation `‖` Q `‖` := Qvr.vtx Q

-- An arrow in a quiver.
-- \lbag \rbag
notation `⟅` Q `⟆` := Qvr.arr Q

-- The source of an arrow.
-- [ \rangle
notation `[` e `⟩` := Qvr.src _ e

-- The destination of an arrow.
-- \langle ]
notation `⟨` e `]` := Qvr.dst _ e

-- A morphism of quivers.
structure Qvr.Mor
    (A : Qvr.{ℓvtx₁ ℓarr₁})
    (B : Qvr.{ℓvtx₂ ℓarr₂})
    : Type ((max ℓvtx₁ ℓarr₁ ℓvtx₂ ℓarr₂) + 1)
:= (vtx : ‖A‖ → ‖B‖)
   (arr : A^.arr → B^.arr)
   (src : ∀ {e : ⟅A⟆}, [arr e⟩ = vtx [e⟩)
   (dst : ∀ {e : ⟅A⟆}, ⟨arr e] = vtx ⟨e])

attribute [simp] Qvr.Mor.src
attribute [simp] Qvr.Mor.dst

-- A morphism of quivers.
-- \Rightarrow\Rightarrow
notation A `⇒⇒` B := Qvr.Mor A B

/-! #brief Every quiver morphism can be treated as a function on vertices.
-/
@[reducible] instance Qvr.Mor.vtx_has_coe_to_fun {A : Qvr.{ℓvtx₁ ℓarr₁}} {B : Qvr.{ℓvtx₂ ℓarr₂}}
    : has_coe_to_fun (Qvr.Mor A B)
:= { F := λ M, ‖A‖ → ‖B‖
   , coe := λ M v, M^.vtx v
   }

-- Action of a quiver morphism on an arrow.
-- \searrow
infix `↘` : 100 := λ {A : Qvr} {B : Qvr} (M : A ⇒⇒ B) (e : ⟅A⟆), M^.arr e



/- ----------------------------------------------------------------------------
Morphisms of quivers.
---------------------------------------------------------------------------- -/

/-! #brief Helper for proving two quiver morphisms are equal.
-/
theorem Qvr.Mor.eq {A : Qvr.{ℓvtx₁ ℓarr₁}} {B : Qvr.{ℓvtx₂ ℓarr₂}}
    : ∀ {M N : A ⇒⇒ B}
        (ωvtx : ∀ (a : ‖A‖), M a = N a)
        (ωarr : ∀ (e : ⟅A⟆), M ↘ e = N ↘ e)
      , M = N
| (Qvr.Mor.mk vtx₁ arr₁ src₁ dst₁) (Qvr.Mor.mk vtx₂ arr₂ src₂ dst₂)
  ωvtx ωarr
:= begin
     assert ωvtx' : vtx₁ = vtx₂, { exact funext ωvtx },
     subst ωvtx',
     assert ωarr' : arr₁ = arr₂, { exact funext ωarr },
     subst ωarr'
   end

/-! #brief The identity quiver morphism.
-/
@[reducible] definition Qvr.Mor.id (A : Qvr.{ℓvtx ℓarr})
    : A ⇒⇒ A
:= { vtx := λ v, v
   , arr := λ e, e
   , src := λ e, rfl
   , dst := λ e, rfl
   }

/-! #brief Composition of quiver morphisms.
-/
@[reducible] definition Qvr.Mor.comp {A : Qvr.{ℓvtx₁ ℓarr₁}} {B : Qvr.{ℓvtx₂ ℓarr₂}} {C : Qvr.{ℓvtx₃ ℓarr₃}}
    (G : B ⇒⇒ C) (F : A ⇒⇒ B)
    : A ⇒⇒ C
:= { vtx := λ v, G (F v)
   , arr := λ e, G ↘ (F ↘ e)
   , src := λ e, by simp
   , dst := λ e, by simp
   }

-- Composition of quiver morphisms.
-- \bigcirc\bigcirc
infixl `◯◯` : 150 := Qvr.Mor.comp

/-! #brief Composition of quiver morphisms is associative.
-/
theorem Qvr.Mor.comp_assoc {A : Qvr.{ℓvtx₁ ℓarr₁}} {B : Qvr.{ℓvtx₂ ℓarr₂}} {C : Qvr.{ℓvtx₃ ℓarr₃}} {D : Qvr.{ℓvtx₄ ℓarr₄}}
    {H : C ⇒⇒ D} {G : B ⇒⇒ C} {F : A ⇒⇒ B}
    : H ◯◯ (G ◯◯ F) = (H ◯◯ G) ◯◯ F
:= rfl

/-! #brief The identity quiver morphism is a left-identity for composition.
-/
theorem Qvr.Mor.comp_id_left {A : Qvr.{ℓvtx₁ ℓarr₁}} {B : Qvr.{ℓvtx₂ ℓarr₂}}
    {F : A ⇒⇒ B}
    : Qvr.Mor.id B ◯◯ F = F
:= begin cases F, apply rfl end

/-! #brief The identity quiver morphism is a right-identity for composition.
-/
theorem Qvr.Mor.comp_id_right {A : Qvr.{ℓvtx₁ ℓarr₁}} {B : Qvr.{ℓvtx₂ ℓarr₂}}
    {F : A ⇒⇒ B}
    : F ◯◯ Qvr.Mor.id A = F
:= begin cases F, apply rfl end



/- ----------------------------------------------------------------------------
The category of quivers.
---------------------------------------------------------------------------- -/

/-! #brief The category of quivers.
-/
@[reducible] definition QvrCat
    : Cat.{((max ℓvtx ℓarr) + 1) ((max ℓvtx ℓarr) + 1)}
:= { obj := Qvr.{ℓvtx ℓarr}
   , hom := Qvr.Mor
   , id := Qvr.Mor.id
   , circ := @Qvr.Mor.comp
   , circ_assoc := @Qvr.Mor.comp_assoc
   , circ_id_left := @Qvr.Mor.comp_id_left
   , circ_id_right := @Qvr.Mor.comp_id_right
   }



/- ----------------------------------------------------------------------------
Boxed arrows.
---------------------------------------------------------------------------- -/

-- A boxed arrow.
structure Qvr.BxArr {Q : Qvr.{ℓvtx ℓarr}} (v₁ v₂ : ‖Q‖) : Type (max 1 ℓvtx ℓarr)
:= (arr : ⟅Q⟆)
   (src : v₁ = [arr⟩)
   (dst : v₂ = ⟨arr])

-- TODO: Fix docstring!
--/-! #brief Every arrow can be used as a boxed arrow.
---/
@[reducible] definition Qvr.BxArr.of_arr {Q : Qvr.{ℓvtx ℓarr}}
    (e : ⟅Q⟆)
    : Qvr.BxArr [e⟩ ⟨e]
:= { arr := e
   , src := rfl
   , dst := rfl
   }

-- A boxed arrow.
-- \lfloor \rfloor
notation `⌊` e `⌋` := Qvr.BxArr.of_arr e

/-! #brief Action of a quiver morphism on a boxed arrow.
-/
@[reducible] definition Qvr.Mor.on_BxArr {Q₁ : Qvr.{ℓvtx₁ ℓarr₁}} {Q₂ : Qvr.{ℓvtx₂ ℓarr₂}}
    (M : Q₁ ⇒⇒ Q₂)
    {v₁ v₂ : ‖Q₁‖}
    (be : Qvr.BxArr v₁ v₂)
    : Qvr.BxArr (M v₁) (M v₂)
:= { arr := M ↘ be^.arr
   , src := by rw [M^.src, -be^.src]
   , dst := by rw [M^.dst, -be^.dst]
   }

-- Action of a quiver morphism on a boxed arrow.
-- \Box\searrow
infix `□↘` : 100 := λ {Q₁ : Qvr} {Q₂ : Qvr} (M : Q₁ ⇒⇒ Q₂) {v₁ v₂ : ‖Q₁‖} (e : Qvr.BxArr v₁ v₂), Qvr.Mor.on_BxArr M e

end qp
