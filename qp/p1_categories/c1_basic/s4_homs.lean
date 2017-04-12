/- -----------------------------------------------------------------------
Boxes of homs in a category.
----------------------------------------------------------------------- -/

import .s1_categories

namespace qp

open stdaux

universe variables ℓ ℓobj ℓhom ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂



/- -----------------------------------------------------------------------
Boxes full of homs.
----------------------------------------------------------------------- -/

/-! #brief Type of dlist used for defining Hom.
-/
@[reducible] definition HomAt (C : Cat.{ℓobj ℓhom})
    : prod C^.obj C^.obj → Sort ℓhom
:= λ cc, C^.hom cc^.fst cc^.snd

/-! #brief A list of homs in a category.
-/
definition HomsList (C : Cat.{ℓobj ℓhom})
    (ccs : list (prod C^.obj C^.obj))
:= dlist (HomAt C) ccs

/-! #brief The nil HomsList.
-/
definition HomsList.nil {C : Cat.{ℓobj ℓhom}}
    : HomsList C []
:= dlist.nil _

/-! #brief Push another hom onto a HomsList.
-/
definition HomsList.cons {C : Cat.{ℓobj ℓhom}}
    {x y : C^.obj} (f : C^.hom x y)
    {ccs : list (prod C^.obj C^.obj)} (tail : HomsList C ccs)
    : HomsList C ((x,y) :: ccs)
:= dlist.cons _ f _ tail

infixr `↗` : 50 := HomsList.cons
notation f `↗↗` := HomsList.cons f HomsList.nil

example {C : Cat.{ℓobj ℓhom}}
        {a₁ a₂ b₁ b₂ c₁ c₂ : C^.obj}
        (fa : C^.hom a₁ a₂)
        (fb : C^.hom b₁ b₂)
        (fc : C^.hom c₁ c₂)
        : HomsList C [(a₁, a₂), (b₁, b₂), (c₁, c₂)]
:= fa ↗ fb ↗ fc ↗↗

/-! #brief Helper for equality of HomsList.cons.
-/
theorem HomsList.eq {C : Cat.{ℓobj ℓhom}}
    {x y : C^.obj} {f₁ f₂ : C^.hom x y}
    {ccs : list (prod C^.obj C^.obj)} {tail₁ tail₂ : HomsList C ccs}
    (ωf : f₁ = f₂)
    (ωtail : tail₁ = tail₂)
    : HomsList.cons f₁ tail₁ = HomsList.cons f₂ tail₂
:= dlist.eq ωf ωtail

/-! #brief Listing the identity homs.
-/
definition HomsList.id {C : Cat.{ℓobj ℓhom}}
    : ∀ (factor : list C^.obj)
      , HomsList C (list.map prod.diag factor)
| [] := HomsList.nil
| (factor :: factors) := HomsList.cons (C^.id factor) (HomsList.id factors)

/-! #brief Fetching a hom out of HomsList.
-/
definition HomsList.get {C : Cat.{ℓobj ℓhom}}
    {ccs : list (prod C^.obj C^.obj)}
    (homs : HomsList C ccs)
    (n : fin (list.length ccs))
    : C^.hom (list.get ccs n)^.fst (list.get ccs n)^.snd
:= dlist.get homs n

/-! #brief Congruence for HomsList.get.
-/
theorem HomsList.congr_get {C : Cat.{ℓobj ℓhom}}
    {ccs : list (prod C^.obj C^.obj)}
    {homs₁ homs₂ : HomsList C ccs}
    (ωhoms : homs₁ = homs₂)
    (n : fin (list.length ccs))
    : HomsList.get homs₁ n = HomsList.get homs₂ n
:= dlist.congr_get ωhoms n

/-! #brief Repeat a hom N times.
-/
definition HomsList.repeat {C : Cat.{ℓobj ℓhom}}
    {x y : C^.obj}
    (f : C^.hom x y) (N : ℕ)
    : HomsList C (list.repeat (x, y) N)
:= dlist.repeat f N

/-! #brief Action of get on repeat.
-/
theorem HomsList.get_repeat {C : Cat.{ℓobj ℓhom}}
    {x y : C^.obj}
    (f : C^.hom x y) {N : ℕ}
    (n : fin N)
    : HomsList.get (HomsList.repeat f N) { val := n^.val, is_lt := begin rw list.length_repeat, exact n^.is_lt end }
       == f
:= by apply @dlist.get_repeat _ (HomAt C)


/- -----------------------------------------------------------------------
Boxes full of homs out of an object.
----------------------------------------------------------------------- -/

/-! #brief Outward homs.
-/
definition HomsOut {C : Cat.{ℓobj ℓhom}}
    (c : C^.obj)
    (factor : list C^.obj)
    : Type (max ℓobj ℓhom)
:= dlist (C^.hom c) factor

/-! #brief The nil HomsOut.
-/
definition HomsOut.nil {C : Cat.{ℓobj ℓhom}}
    {c : C^.obj}
    : HomsOut c []
:= dlist.nil _

/-! #brief Push another hom onto a HomsOut.
-/
definition HomsOut.cons {C : Cat.{ℓobj ℓhom}}
    {x c : C^.obj} (f : C^.hom c x)
    {factor : list C^.obj} (tail : HomsOut c factor)
    : HomsOut c (x :: factor)
:= dlist.cons _ f _ tail

infixr `↗←` : 50 := HomsOut.cons
notation f `↗←↗` := HomsOut.cons f HomsOut.nil


/-! #brief Composition with outward homs.
-/
definition HomsOut.comp {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor : list C^.obj}
    (proj : HomsOut c factor)
    {c' : C^.obj} (f : C^.hom c' c)
    : HomsOut c' factor
:= dlist.map (λ a j, C^.circ j f) proj

/-! #brief HomsOut.comp distributes over composition of homs.
-/
definition HomsOut.comp_circ {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor : list C^.obj}
    (proj : HomsOut c factor)
    {c₁ c₂ : C^.obj} (g : C^.hom c₂ c) (f : C^.hom c₁ c₂)
    : HomsOut.comp proj (C^.circ g f)
       = HomsOut.comp (HomsOut.comp proj g) f
:= begin
     unfold HomsOut.comp,
     apply eq.symm,
     refine eq.trans (dlist.map_map _ _) _,
     refine congr_arg (λ f, dlist.map f proj) _,
     apply funext, intro a, apply funext, intro j,
     apply eq.symm C^.circ_assoc
   end

/-! #brief Composition of a HomsList with a HomsOut.
-/
definition homs_comp_out {C : Cat.{ℓobj ℓhom}}
    : ∀ {ccs : list (prod C^.obj C^.obj)}
        (fns : HomsList C ccs)
        {c : C^.obj}
        (c_proj : HomsOut c (list.map prod.fst ccs))
      , HomsOut c (list.map prod.snd ccs)
:= λ ccs fns c c_proj
   , begin
       induction ccs with cc ccs rec,
       { apply dlist.nil },
       { cases fns with cc f ccs fns',
         cases cc with c₁ c₂,
         cases c_proj with c₁ p ccs c_proj',
         apply dlist.cons _ (C^.circ f p) _ (rec fns' c_proj')
       }
     end

/-! #brief Fetching a hom out of HomsOut.
-/
definition HomsOut.get {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor : list C^.obj}
    (proj : HomsOut c factor)
    (n : fin (list.length factor))
    : C^.hom c (list.get factor n)
:= dlist.get proj n

/-! #brief get is injective.
-/
theorem HomsOut.get.inj {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor : list C^.obj}
    (proj₁ proj₂ : HomsOut c factor)
    (ω : HomsOut.get proj₁ = HomsOut.get proj₂)
    : proj₁ = proj₂
:= dlist.get.inj ω

/-! #brief get on comp.
-/
theorem HomsOut.get_comp {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor : list C^.obj}
    {proj : HomsOut c factor}
    {c' : C^.obj} {f : C^.hom c' c}
    {n : fin (list.length factor)}
    : HomsOut.get (HomsOut.comp proj f) n = C^.circ (HomsOut.get proj n) f
:= dlist.get_map _ _ _

/-! #brief An inverse to HomsOut.get.
-/
definition HomsOut.enum {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor : list C^.obj}
    (f : ∀ (n : fin (list.length factor)), C^.hom c (list.get factor n))
    : HomsOut c factor
:= dlist.enum f

/-! #brief enum and get are inverses.
-/
theorem HomsOut.enum_get {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor : list C^.obj}
    (proj : HomsOut c factor)
    : HomsOut.enum (HomsOut.get proj) = proj
:= dlist.enum_get

/-! #brief enum and get are inverses.
-/
theorem HomsOut.get_enum {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor : list C^.obj}
    (f : ∀ (n : fin (list.length factor)), C^.hom c (list.get factor n))
    (n : fin (list.length factor))
    : HomsOut.get (HomsOut.enum f) n = f n
:= dlist.get_enum _ _

/-! #brief Appending lists of outward homs.
-/
definition HomsOut.append {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor₁ factor₂ : list C^.obj}
    (proj₁ : HomsOut c factor₁)
    (proj₂ : HomsOut c factor₂)
    : HomsOut c (factor₁ ++ factor₂)
:= dlist.append proj₁ proj₂

/-! #brief Splitting lists of outward homs.
-/
definition HomsOut.split_left {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor₁ factor₂ : list C^.obj}
    (proj : HomsOut c (factor₁ ++ factor₂))
    : HomsOut c factor₁
:= dlist.split_left factor₁ proj

/-! #brief Splitting lists of outward homs.
-/
definition HomsOut.split_right {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor₁ factor₂ : list C^.obj}
    (proj : HomsOut c (factor₁ ++ factor₂))
    : HomsOut c factor₂
:= dlist.split_right factor₁ proj

/-! #brief Equality of HomsOut.append
-/
theorem HomsOut.append_eq {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor₁ factor₂ : list C^.obj}
    (proj₁ proj₂ : HomsOut c (factor₁ ++ factor₂))
    (ωleft : HomsOut.split_left proj₁ = HomsOut.split_left proj₂)
    (ωright : HomsOut.split_right proj₁ = HomsOut.split_right proj₂)
    : proj₁ = proj₂
:= dlist.append_eq ωleft ωright

/-! #brief Action of split_left on append.
-/
theorem HomsOut.split_left_append {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor₁ factor₂ : list C^.obj}
    (proj₁ : HomsOut c factor₁)
    (proj₂ : HomsOut c factor₂)
    : HomsOut.split_left (HomsOut.append proj₁ proj₂)
       = proj₁
:= dlist.split_left_append

/-! #brief Action of split_right on append.
-/
theorem HomsOut.split_right_append {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor₁ factor₂ : list C^.obj}
    (proj₁ : HomsOut c factor₁)
    (proj₂ : HomsOut c factor₂)
    : HomsOut.split_right (HomsOut.append proj₁ proj₂)
       = proj₂
:= dlist.split_right_append

/-! #brief Action of split_left on comp.
-/
theorem HomsOut.split_left_comp {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor₁ factor₂ : list C^.obj}
    (proj : HomsOut c (factor₁ ++ factor₂))
    {c' : C^.obj} (f : C^.hom c' c)
    : HomsOut.split_left (HomsOut.comp proj f)
       = HomsOut.comp (HomsOut.split_left proj) f
:= dlist.split_left_map _

/-! #brief Action of split_right on comp.
-/
theorem HomsOut.split_right_comp {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor₁ factor₂ : list C^.obj}
    (proj : HomsOut c (factor₁ ++ factor₂))
    {c' : C^.obj} (f : C^.hom c' c)
    : HomsOut.split_right (HomsOut.comp proj f)
       = HomsOut.comp (HomsOut.split_right proj) f
:= dlist.split_right_map _

/-! #brief Action of get on an append.
-/
theorem HomsOut.get_append {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor₁ factor₂ : list C^.obj}
    (proj₁ : HomsOut c factor₁)
    (proj₂ : HomsOut c factor₂)
    (n : ℕ) (ωn : n < list.length factor₁)
    : HomsOut.get (HomsOut.append proj₁ proj₂) (fin.mk n (list.length.grow_left ωn))
       == HomsOut.get proj₁ (fin.mk n ωn)
:= dlist.get_append

/-! #brief Action of get on split_left.
-/
theorem HomsOut.get_split_left {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor₁ factor₂ : list C^.obj}
    {proj : HomsOut c (factor₁ ++ factor₂)}
    {n : ℕ} {ωn : n < list.length factor₁}
    : HomsOut.get (HomsOut.split_left proj) (fin.mk n ωn)
       = cast_hom list.get_append_left
          ∘∘ HomsOut.get proj (fin.mk n (list.length.grow_left ωn))
:= begin
     apply eq_of_heq,
     refine heq.trans _ (heq.symm (cast_hom.circ_left_heq _ _)),
     apply dlist.get_split_left
   end

/-! #brief Action of get on split_right.
-/
theorem HomsOut.get_split_right {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor₁ factor₂ : list C^.obj}
    {proj : HomsOut c (factor₁ ++ factor₂)}
    {n : ℕ} {ωn : n < list.length factor₂}
    : HomsOut.get (HomsOut.split_right proj) (fin.mk n ωn)
       = cast_hom list.get_append_right
          ∘∘ HomsOut.get proj (fin.mk (n + list.length factor₁) (list.length.grow_right ωn))
:= begin
     apply eq_of_heq,
     refine heq.trans _ (heq.symm (cast_hom.circ_left_heq _ _)),
     apply dlist.get_split_right
   end



/- -----------------------------------------------------------------------
Boxes full of homs into an object.
----------------------------------------------------------------------- -/

/-! #brief Inward homs.
-/
definition HomsIn {C : Cat.{ℓobj ℓhom}}
    (factor : list C^.obj)
    (c : C^.obj)
    : Type (max ℓobj ℓhom)
:= dlist (λ x, C^.hom x c) factor

/-! #brief The nil HomsIn.
-/
definition HomsIn.nil {C : Cat.{ℓobj ℓhom}}
    {c : C^.obj}
    : HomsIn [] c
:= dlist.nil _

/-! #brief Push another hom onto a HomsIn.
-/
definition HomsIn.cons {C : Cat.{ℓobj ℓhom}}
    {x c : C^.obj} (f : C^.hom x c)
    {factor : list C^.obj} (tail : HomsIn factor c)
    : HomsIn (x :: factor) c
:= dlist.cons _ f _ tail

infixr `↗→` : 50 := HomsIn.cons
notation f `↗→↗` := HomsIn.cons f HomsIn.nil

/-! #brief Repeat a hom N times.
-/
definition HomsIn.repeat {C : Cat.{ℓobj ℓhom}}
    {x y : C^.obj}
    (f : C^.hom x y) (N : ℕ)
    : HomsIn (list.repeat x N) y
:= dlist.repeat f N

/-! #brief Converting a list of OverObj's into a HomsIn.
-/
definition HomsIn.of_list_OverObj {C : Cat.{ℓobj ℓhom}} {X : C^.obj}
    : ∀ (factors : list (OverObj C X))
      , HomsIn (list.map OverObj.dom factors) X
| [] := HomsIn.nil
| (O :: OO) := HomsIn.cons O^.hom (HomsIn.of_list_OverObj OO)

/-! #brief Composition with inward homs.
-/
definition HomsIn.comp {C : Cat.{ℓobj ℓhom}} {c₁ : C^.obj}
    {c₂ : C^.obj} (g : C^.hom c₁ c₂)
    {factor : list C^.obj}
    (proj : HomsIn factor c₁)
    : HomsIn factor c₂
:= dlist.map (λ a j, C^.circ g j) proj

/-! #brief HomsIn.comp distributes over composition of homs.
-/
definition HomsIn.comp_circ {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {c₁ c₂ : C^.obj} (g : C^.hom c₁ c₂) (f : C^.hom c c₁)
    {factor : list C^.obj}
    (proj : HomsIn factor c)
    : HomsIn.comp (C^.circ g f) proj
       = HomsIn.comp g (HomsIn.comp f proj)
:= begin
     unfold HomsIn.comp,
     apply eq.symm,
     refine eq.trans (dlist.map_map _ _) _,
     refine congr_arg (λ f, dlist.map f proj) _,
     apply funext, intro a, apply funext, intro j,
     apply C^.circ_assoc
   end

/-! #brief Composition of a HomsList with a HomsIn.
-/
definition homs_comp_in {C : Cat.{ℓobj ℓhom}}
    : ∀ {ccs : list (prod C^.obj C^.obj)}
        {c : C^.obj}
        (c_proj : HomsIn (list.map prod.snd ccs) c)
        (fns : HomsList C ccs)
      , HomsIn (list.map prod.fst ccs) c
:= λ ccs c c_proj fns
   , begin
       induction ccs with cc ccs rec,
       { apply dlist.nil },
       { cases fns with cc f ccs fns',
         cases cc with c₁ c₂,
         cases c_proj with c₁ p ccs c_proj',
         refine dlist.cons _ (C^.circ p f) _ (rec c_proj' fns')
       }
     end

/-! #brief Fetching a hom out of HomsIn.
-/
definition HomsIn.get {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor : list C^.obj}
    (proj : HomsIn factor c)
    (n : fin (list.length factor))
    : C^.hom (list.get factor n) c
:= dlist.get proj n

/-! #brief get is injective.
-/
theorem HomsIn.get.inj {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor : list C^.obj}
    (proj₁ proj₂ : HomsIn factor c)
    (ω : HomsIn.get proj₁ = HomsIn.get proj₂)
    : proj₁ = proj₂
:= dlist.get.inj ω

/-! #brief get on comp.
-/
theorem HomsIn.get_comp {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor : list C^.obj}
    {proj : HomsIn factor c}
    {c' : C^.obj} {g : C^.hom c c'}
    {n : fin (list.length factor)}
    : HomsIn.get (HomsIn.comp g proj) n = C^.circ g (HomsIn.get proj n)
:= dlist.get_map (λ (a : ⟦C⟧) (j : ⟦C : a →→ c⟧), @Cat.circ C _ _ _ g j) _ _

/-! #brief An inverse to HomsIn.get.
-/
definition HomsIn.enum {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor : list C^.obj}
    (f : ∀ (n : fin (list.length factor)), C^.hom (list.get factor n) c)
    : HomsIn factor c
:= dlist.enum f

/-! #brief enum and get are inverses.
-/
theorem HomsIn.enum_get {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor : list C^.obj}
    (proj : HomsIn factor c)
    : HomsIn.enum (HomsIn.get proj) = proj
:= dlist.enum_get

/-! #brief enum and get are inverses.
-/
theorem HomsIn.get_enum {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor : list C^.obj}
    (f : ∀ (n : fin (list.length factor)), C^.hom (list.get factor n) c)
    (n : fin (list.length factor))
    : HomsIn.get (HomsIn.enum f) n = f n
:= by apply @dlist.get_enum _ (λ x, C^.hom x c)

/-! #brief Appending lists of inward homs.
-/
definition HomsIn.append {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor₁ factor₂ : list C^.obj}
    (proj₁ : HomsIn factor₁ c)
    (proj₂ : HomsIn factor₂ c)
    : HomsIn (factor₁ ++ factor₂) c
:= dlist.append proj₁ proj₂

/-! #brief Splitting lists of inward homs.
-/
definition HomsIn.split_left {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor₁ factor₂ : list C^.obj}
    (proj : HomsIn (factor₁ ++ factor₂) c)
    : HomsIn factor₁ c
:= dlist.split_left factor₁ proj

/-! #brief Splitting lists of inward homs.
-/
definition HomsIn.split_right {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor₁ factor₂ : list C^.obj}
    (proj : HomsIn (factor₁ ++ factor₂) c)
    : HomsIn factor₂ c
:= dlist.split_right factor₁ proj

/-! #brief Equality of HomsIn.append
-/
theorem HomsIn.append_eq {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor₁ factor₂ : list C^.obj}
    (proj₁ proj₂ : HomsIn (factor₁ ++ factor₂) c)
    (ωleft : HomsIn.split_left proj₁ = HomsIn.split_left proj₂)
    (ωright : HomsIn.split_right proj₁ = HomsIn.split_right proj₂)
    : proj₁ = proj₂
:= dlist.append_eq ωleft ωright

/-! #brief Action of split_left on append.
-/
theorem HomsIn.split_left_append {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor₁ factor₂ : list C^.obj}
    (proj₁ : HomsIn factor₁ c)
    (proj₂ : HomsIn factor₂ c)
    : HomsIn.split_left (HomsIn.append proj₁ proj₂)
       = proj₁
:= dlist.split_left_append

/-! #brief Action of split_right on append.
-/
theorem HomsIn.split_right_append {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor₁ factor₂ : list C^.obj}
    (proj₁ : HomsIn factor₁ c)
    (proj₂ : HomsIn factor₂ c)
    : HomsIn.split_right (HomsIn.append proj₁ proj₂)
       = proj₂
:= dlist.split_right_append

/-! #brief Action of split_left on comp.
-/
theorem HomsIn.split_left_comp {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor₁ factor₂ : list C^.obj}
    (proj : HomsIn (factor₁ ++ factor₂) c)
    {c' : C^.obj} (f : C^.hom c c')
    : HomsIn.split_left (HomsIn.comp f proj)
       = HomsIn.comp f (HomsIn.split_left proj)
:= dlist.split_left_map _

/-! #brief Action of split_right on comp.
-/
theorem HomsIn.split_right_comp {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor₁ factor₂ : list C^.obj}
    (proj : HomsIn (factor₁ ++ factor₂) c)
    {c' : C^.obj} (f : C^.hom c c')
    : HomsIn.split_right (HomsIn.comp f proj)
       = HomsIn.comp f (HomsIn.split_right proj)
:= dlist.split_right_map _

/-! #brief Action of get on an append.
-/
theorem HomsIn.get_append {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor₁ factor₂ : list C^.obj}
    (proj₁ : HomsIn factor₁ c)
    (proj₂ : HomsIn factor₂ c)
    (n : ℕ) (ωn : n < list.length factor₁)
    : HomsIn.get (HomsIn.append proj₁ proj₂) (fin.mk n (list.length.grow_left ωn))
       == HomsIn.get proj₁ (fin.mk n ωn)
:= by apply @dlist.get_append _ (λ x, C^.hom x c)

/-! #brief Action of get on split_left.
-/
theorem HomsIn.get_split_left {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor₁ factor₂ : list C^.obj}
    {proj : HomsIn (factor₁ ++ factor₂) c}
    {n : ℕ} {ωn : n < list.length factor₁}
    : HomsIn.get (HomsIn.split_left proj) (fin.mk n ωn)
       = HomsIn.get proj (fin.mk n (list.length.grow_left ωn))
          ∘∘ cast_hom (eq.symm list.get_append_left)
:= begin
     apply eq_of_heq,
     refine heq.trans _ (heq.symm (cast_hom.circ_right_heq _ _)),
     apply @dlist.get_split_left _ (λ x, C^.hom x c)
   end

/-! #brief Action of get on split_right.
-/
theorem HomsIn.get_split_right {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor₁ factor₂ : list C^.obj}
    {proj : HomsIn (factor₁ ++ factor₂) c}
    {n : ℕ} {ωn : n < list.length factor₂}
    : HomsIn.get (HomsIn.split_right proj) (fin.mk n ωn)
       = HomsIn.get proj (fin.mk (n + list.length factor₁) (list.length.grow_right ωn))
          ∘∘ cast_hom (eq.symm list.get_append_right)
:= begin
     apply eq_of_heq,
     refine heq.trans _ (heq.symm (cast_hom.circ_right_heq _ _)),
     apply @dlist.get_split_right _ (λ x, C^.hom x c)
   end

/-! #brief Composition of a HomsIn with a HomsOut.
-/
definition homs_in_comp_out {C : Cat.{ℓobj ℓhom}}
    : ∀ {factor : list C^.obj}
        {c₁ c₂ : C^.obj}
        (hin : HomsIn factor c₂)
        (hout : HomsOut c₁ factor)
      , HomsList C (list.repeat (c₁, c₂) (list.length factor))
:= λ factor c₁ c₂ hin hout
   , begin
       induction factor with x factor rec,
       { apply dlist.nil },
       { cases hin with x fin factor hin',
         cases hout with x fout factor hout',
         refine dlist.cons _ (C^.circ fin fout) _ (rec hin' hout')
       }
     end

/-! #brief Action of get on homs_in_comp_out.
-/
theorem get_homs_in_comp_out {C : Cat.{ℓobj ℓhom}}
    {factor : list C^.obj}
    {c₁ c₂ : C^.obj}
    (hin : HomsIn factor c₂)
    (hout : HomsOut c₁ factor)
    {n : fin (list.length factor)}
    : HomsList.get (homs_in_comp_out hin hout) { val := n^.val, is_lt := begin rw list.length_repeat, exact n^.is_lt end }
       == C^.circ (HomsIn.get hin n) (HomsOut.get hout n)
:= begin
     induction factor with x factor rec,
     { exact fin.zero_elim n },
     { cases hin with x fin factor hin',
       cases hout with x fout factor hout',
       cases n with n ωn,
       cases n with n,
       { trivial },
       { refine @rec hin' hout' { val := n, is_lt := _ }}
     }
   end

end qp
