/- ----------------------------------------------------------------------------
The Yoneda embedding and the Yoneda lemma.
---------------------------------------------------------------------------- -/

import .basic

namespace qp
universe variables ℓobj ℓhom



/- ----------------------------------------------------------------------------
The Yoneda embedding.
---------------------------------------------------------------------------- -/

/-! #brief The Yoneda embedding of an object.
-/
definition YonedaFunObj {C : Cat.{ℓobj ℓhom}} (c : [[C]])
    : [[PreShCat C SortCat.{ℓhom}]]
:= { obj := λ x, x →→ c
   , hom := λ x y f g, g ∘∘ f
   , hom_id := λ x , begin apply pfunext, intro f, dsimp, simp end
   , hom_circ := λ x y z g f, begin apply pfunext, intro h, dsimp, simp [Cat.circ_assoc] end
   }

@[simp] theorem YonedaFunObj.simp_obj {C : Cat.{ℓobj ℓhom}} {c : [[C]]}
    (x : [[{{C}}⁻¹]])
    : YonedaFunObj c x = x →→ c
:= rfl

@[simp] theorem YonedaFunObj.simp_hom {C : Cat.{ℓobj ℓhom}} {c : [[C]]}
    {x y : [[{{C}}⁻¹]]} (f : ({{C}}⁻¹)^.hom x y) (g : C^.hom x c)
    : (YonedaFunObj c ↗ f) g = C^.circ g f
:= rfl

/-! #brief The Yoneda embedding of a hom.
-/
definition YonedaFunHom {C : Cat.{ℓobj ℓhom}} {x y : [[C]]}
    (g : x →→ y)
    : YonedaFunObj x ↣↣ YonedaFunObj y
:= { component := λ x f, g ∘∘ f
   , transport := λ x y g, begin dsimp, apply pfunext, intro f, apply C^.circ_assoc, end
   }

@[simp] theorem YonedaFunHom.simp_component {C : Cat.{ℓobj ℓhom}} {x y : [[C]]}
    (g : x →→ y) (z : [[{{C}}⁻¹]]) (f : YonedaFunObj x z)
    : (YonedaFunHom g) z f = g ∘∘ f
:= rfl

/-! #brief The Yoneda embedding of a category into its presheaf category.
-/
definition YonedaFun (C : Cat.{ℓobj ℓhom})
    : C ⇉⇉ PreShCat C SortCat.{ℓhom}
:= { obj := YonedaFunObj
   , hom := λ x y g, YonedaFunHom g
   , hom_id := λ x, begin apply NatTrans.eq, intro y, rw [NatTrans.id.simp_component], apply pfunext, intro g, simp end
   , hom_circ
      := λ x y z g f
         , begin
             apply NatTrans.eq,
             intro w,
             apply pfunext,
             intro h,
             rw [YonedaFunHom.simp_component],
             apply eq.symm (C^.circ_assoc)
           end
   }

@[simp] theorem YonedaFun.simp_obj {C : Cat.{ℓobj ℓhom}}
    (c : [[C]])
    : YonedaFun C c = YonedaFunObj c
:= rfl

@[simp] theorem YonedaFun.simp_hom {C : Cat.{ℓobj ℓhom}}
    {x y : [[C]]} (f : x →→ y)
    : YonedaFun C ↗ f = YonedaFunHom f
:= rfl

/-! #brief The Yoneda representation of a natural transformation.
-/
@[reducible] definition YonedaFun.represent {C : Cat.{ℓobj ℓhom}}
    (X : [[PreShCat C SortCat]])
    (c : [[C]])
    (η : YonedaFun C c ↣↣ X)
    : X c
:= η c ⟨⟨c⟩⟩

/-! #brief The natural transformation induced by a Yoneda representation.
-/
@[reducible] definition YonedaFun.construct {C : Cat.{ℓobj ℓhom}}
    (X : [[PreShCat C SortCat]])
    (c : [[C]])
    (r : X c)
    : YonedaFun C c ↣↣ X
:= { component := λ x g, (X ↗ g) r
   , transport := λ x y g
                  , begin
                      apply pfunext,
                      intro f,
                      dsimp [YonedaFun],
                      rw X^.hom_circ
                    end
   }

/-! #brief YonedaFun.represent and YonedaFun.construct are inverses of one another.
-/
@[simp] theorem YonedaFun.represent_construct {C : Cat.{ℓobj ℓhom}}
    (X : [[PreShCat C SortCat]])
    (c : [[C]])
    (r : X c)
    : YonedaFun.represent X c (YonedaFun.construct X c r) = r
:= begin dsimp, rw X^.hom_id end

/-! #brief YonedaFun.construct and YonedaFun.represent are inverses of one another.
-/
@[simp] theorem YonedaFun.construct_represent {C : Cat.{ℓobj ℓhom}}
    (X : [[PreShCat C SortCat]])
    (c : [[C]])
    (η : YonedaFun C c ↣↣ X)
    : YonedaFun.construct X c (YonedaFun.represent X c η) = η
:= begin
     apply NatTrans.eq, intro y,
     dsimp,
     apply pfunext, intro g,
     assert lem₁ : η y g = η y (⟨⟨c⟩⟩ ∘∘ g),
     { rw Cat.circ_id_left },
     refine eq.symm (eq.trans lem₁ _),
     apply congr_fun η^.transport
   end

end qp
