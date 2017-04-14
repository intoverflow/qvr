/- -----------------------------------------------------------------------
The topos of trees.
----------------------------------------------------------------------- -/

import ..c1_basic
import ..c2_limits

namespace qp

open stdaux

universe variables ℓobjx ℓhomx

/-! #brief The topos of trees.
-/
definition TreeTopos : Cat
:= PreShCat NatCat

/-! #brief Action of the later endofunctor on objects.
-/
definition LaterObj.obj
    (F : TreeTopos^.obj)
    : ∀ (n : ℕ), Type
| 0 := punit
| (nat.succ n) := F^.obj n

/-! #brief Action of the later endofunctor on objects.
-/
definition LaterObj.hom
    (F : TreeTopos^.obj)
    : ∀ (n₂ n₁ : ℕ) (ωn : n₁ ≤ n₂)
      , LaterObj.obj F n₂ → LaterObj.obj F n₁
| n₂ 0 ωn x := punit.star
| 0 (nat.succ n₁) ωn x := false.rec _ (by cases ωn)
| (nat.succ n₂) (nat.succ n₁) ωn x := F^.hom (nat.le_of_succ_le_succ ωn) x

/-! #brief Action of the later endofunctor on objects.
-/
theorem LaterObj.hom.id
    (F : TreeTopos^.obj)
    : ∀ (n : ℕ)
      , LaterObj.hom F n n (nat.le_refl n) = @id (LaterObj.obj F n)
| 0 := begin apply funext, intro u, cases u, trivial end
| (nat.succ n) := F^.hom_id

/-! #brief Action of the later endofunctor on objects.
-/
theorem LaterObj.hom.circ
    (F : TreeTopos^.obj)
    : ∀ (n₃ n₂ n₁ : ℕ) (ωn₁₂ : n₁ ≤ n₂) (ωn₂₃ : n₂ ≤ n₃)
      , LaterObj.hom F n₃ n₁ (nat.le_trans ωn₁₂ ωn₂₃)
         = λ x, LaterObj.hom F n₂ n₁ ωn₁₂ (LaterObj.hom F n₃ n₂ ωn₂₃ x)
| 0 0 0 ωn₁₂ ωn₂₃ := rfl
| 0 0 (nat.succ n₁) ωn₁₂ ωn₂₃ := rfl
| 0 (nat.succ n₂) 0 ωn₁₂ ωn₂₃ := rfl
| (nat.succ n₃) 0 0 ωn₁₂ ωn₂₃ := rfl
| 0 (nat.succ n₂) (nat.succ n₁) ωn₁₂ ωn₂₃ := by cases ωn₂₃
| (nat.succ n₃) 0 (nat.succ n₁) ωn₁₂ ωn₂₃ := by cases ωn₁₂
| (nat.succ n₃) (nat.succ n₂) 0 ωn₁₂ ωn₂₃ := rfl
| (nat.succ n₃) (nat.succ n₂) (nat.succ n₁) ωn₁₂ ωn₂₃ := F^.hom_circ

/-! #brief Action of the later endofunctor on objects.
-/
definition LaterObj
    (F : TreeTopos^.obj)
    : TreeTopos^.obj
:= { obj := LaterObj.obj F
   , hom := LaterObj.hom F
   , hom_id := LaterObj.hom.id F
   , hom_circ := LaterObj.hom.circ F
   }

/-! #brief Action of the later endofunctor on homs.
-/
definition LaterHom.com
    {F₁ F₂ : TreeTopos^.obj}
    (η : TreeTopos^.hom F₁ F₂)
    : ∀ (n : ℕ)
      , LaterObj.obj F₁ n → LaterObj.obj F₂ n
| 0 := id
| (nat.succ n) := η^.com n

/-! #brief Action of the later endofunctor on homs.
-/
theorem LaterHom.natural
    {F₁ F₂ : TreeTopos^.obj}
    (η : TreeTopos^.hom F₁ F₂)
    : ∀ (n₂ n₁ : ℕ) (ωn : n₁ ≤ n₂)
      , (λ x, LaterHom.com η n₁ (LaterObj.hom F₁ n₂ n₁ ωn x))
         = λ x, LaterObj.hom F₂ n₂ n₁ ωn (LaterHom.com η n₂ x)
| 0 0 ωn := rfl
| 0 (nat.succ n₁) ωn := by cases ωn
| (nat.succ n₂) 0 ωn := rfl
| (nat.succ n₂) (nat.succ n₁) ωn := η^.natural


/-! #brief Action of the later endofunctor on homs.
-/
definition LaterHom
    (F₁ F₂ : TreeTopos^.obj)
    (η : TreeTopos^.hom F₁ F₂)
    : TreeTopos^.hom (LaterObj F₁) (LaterObj F₂)
:= { com := LaterHom.com η
   , natural := LaterHom.natural η
   }

/-! #brief The later endofunctor.
-/
definition LaterFun : Fun TreeTopos TreeTopos
:= { obj := LaterObj
   , hom := LaterHom
   , hom_id
      := λ F
         , begin
             apply NatTrans.eq,
             apply funext, intro n, cases n,
             { trivial },
             { trivial }
           end
   , hom_circ
      := λ F₁ F₂ F₃ η₂₃ η₁₂
         , begin
             apply NatTrans.eq,
             apply funext, intro n, cases n,
             { trivial },
             { trivial }
           end
   }

/-! #brief The left adjoint of the later endofunctor.
-/
definition SoonerFun
    : Fun TreeTopos TreeTopos
:= { obj := λ F, { obj := λ n, F^.obj (nat.succ n)
                 , hom := λ n₂ n₁ ωn, F^.hom (nat.succ_le_succ ωn)
                 , hom_id := λ n, F^.hom_id
                 , hom_circ := λ n₃ n₂ n₁ ωn₁₂ ωn₂₃, F^.hom_circ
                 }
   , hom := λ F₁ F₂ η, { com := λ n, η^.com (nat.succ n)
                      , natural := λ n₂ n₁ ωn, η^.natural
                      }
   , hom_id
      := λ F
         , begin
             apply NatTrans.eq,
             apply funext, intro n,
             trivial
           end
   , hom_circ
      := λ F₁ F₂ F₃ η₂₃ η₁₂
         , begin
             apply NatTrans.eq,
             apply funext, intro n,
             trivial
           end
   }

/-! #brief SoonerFun and LaterFun are adjoint.
-/
definition SoonerFun_LaterFun.adj
    : Adj SoonerFun LaterFun
:= { counit
      := { com := λ F, { com := λ n x, x
                       , natural := λ n₂ n₁ f, funext (λ x, rfl)
                       }
         , natural := λ F₁ F₂ η, NatTrans.eq (funext (λ n, funext (λ x, rfl)))
         }
   , unit
      := { com := λ F, { com := λ n x, cast sorry x
                       , natural := λ n₂ n₁ f, funext (λ x, sorry)
                       }
         , natural := λ F₁ F₂ η, NatTrans.eq (funext (λ n, funext (λ x, sorry)))
         }
   , id_left := λ F, NatTrans.eq sorry
   , id_right := λ F, NatTrans.eq sorry
   }

/-! #brief LaterFun preserves all limits.
-/
definition LaterFun.PresLimit
    {X : Cat.{ℓobjx ℓhomx}} (F : Fun X TreeTopos)
    : PresLimit F LaterFun
:= Adj.right.PresLimit SoonerFun_LaterFun.adj F

/-! #brief The next natural transformation.
-/
definition NextTrans.com (X : TreeTopos^.obj)
    : ∀ (n : ℕ)
      , X^.obj n → LaterObj.obj X n
| 0 := λ u, punit.star
| (nat.succ n) := X^.hom (nat.le_succ n)

/-! #brief The next natural transformation.
-/
theorem NextTrans.natural (X : TreeTopos^.obj)
    : ∀ (n₂ n₁ : ℕ) (ωn : n₁ ≤ n₂)
      , Cat.circ LeanCat (NextTrans.com X n₁) (X^.hom ωn)
         = Cat.circ LeanCat (LaterObj.hom X n₂ n₁ ωn) (NextTrans.com X n₂)
| 0 0 ωn := rfl
| 0 (nat.succ n₁) ωn := by cases ωn
| (nat.succ n₂) 0 ωn := rfl
| (nat.succ n₂) (nat.succ n₁) ωn
:= begin
     refine eq.trans (eq.symm X^.hom_circ) _,
     refine eq.trans _ X^.hom_circ,
     trivial
   end

/-! #brief The next natural transformation.
-/
definition NextTrans (X : TreeTopos^.obj)
    : TreeTopos^.hom X (LaterFun^.obj X)
:= { com := NextTrans.com X
   , natural := NextTrans.natural X
   }

end qp
