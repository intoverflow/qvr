/- -----------------------------------------------------------------------
Products and co-products.
----------------------------------------------------------------------- -/

import .s1_limits

namespace qp

open stdaux

universe variables ℓ ℓobj ℓhom ℓobj₁ ℓhom₁ ℓobj₂ ℓhom₂



/- -----------------------------------------------------------------------
Products.
----------------------------------------------------------------------- -/

/-! #brief The product diagram.
-/
definition ProductDrgm (C : Cat.{ℓobj ℓhom}) {A : Type ℓ}
    (factor : A → C^.obj)
    : Fun (ObjCat A) C
:= { obj := λ a, factor a
   , hom := λ a₁ a₂ f, begin cases f, exact C^.id (factor a₁) end
   , hom_id := λ a, rfl
   , hom_circ := λ a₁ a₂ a₃ g f
                 , begin
                     cases g, cases f, exact eq.symm C^.circ_id_left
                   end
   }

/-! #brief A cone over a product.
-/
definition ProductCone (C : Cat.{ℓobj ℓhom}) {A : Type ℓ}
    (factor : A → C^.obj)
    : Type (max ℓ ℓobj ℓhom)
:= Cone (ProductDrgm C factor)

/-! #brief Helper for making a product cone.
-/
definition ProductCone.mk {C : Cat.{ℓobj ℓhom}} {A : Type ℓ}
    {factor : A → C^.obj}
    (c : C^.obj)
    (proj : ∀ (a : A), C^.hom c (factor a))
    : ProductCone C factor
:= { obj := c
   , hom := proj
   , comm := λ a₁ a₂ f, begin cases f, exact eq.symm C^.circ_id_left end
   }

/-! #brief A product in a category.
-/
@[class] definition HasProduct (C : Cat.{ℓobj ℓhom}) {A : Type ℓ}
    (factor : A → C^.obj)
:= HasLimit (ProductDrgm C factor)

instance HasProduct.HasLimit {C : Cat.{ℓobj ℓhom}} {A : Type ℓ}
    (factor : A → C^.obj)
    [factor_HasProduct : HasProduct C factor]
    : HasLimit (ProductDrgm C factor)
:= factor_HasProduct

/-! #brief Helper for showing a category has a product.
-/
definition HasProduct.show (C : Cat.{ℓobj ℓhom}) {A : Type ℓ}
    {factor : A → C^.obj}
    (p : C^.obj)
    (proj : ∀ (a : A), C^.hom p (factor a))
    (univ
      : ∀ (c : C^.obj) (hom : ∀ (a : A), C^.hom c (factor a))
        , C^.hom c p)
    (ωuniv
      : ∀ (c : C^.obj) (hom : ∀ (a : A), C^.hom c (factor a))
           (a : A)
        , hom a = C^.circ (proj a) (univ c hom))
    (ωuniq
      : ∀ (c : C^.obj) (hom : ∀ (a : A), C^.hom c (factor a))
           (h : C^.hom c p) (ωh : ∀ {a : A}, hom a = C^.circ (proj a) h)
        , h = univ c hom)
    : HasProduct C factor
:= HasLimit.show p proj (λ x₁ x₂ f, begin cases f, exact eq.symm C^.circ_id_left end)
    (λ c hom ωcomm, univ c hom)
    (λ c hom ωcomm a, ωuniv c hom a)
    (λ c hom ωcomm h ωh, ωuniq c hom h @ωh)

/-! #brief Products are cones.
-/
definition product.cone (C : Cat.{ℓobj ℓhom}) {A : Type ℓ}
    (factor : A → C^.obj)
    [factor_HasProduct : HasProduct C factor]
    : ProductCone C factor
:= limit.cone (ProductDrgm C factor)

/-! #brief The product of a collection of objects.
-/
definition product (C : Cat.{ℓobj ℓhom}) {A : Type ℓ}
    (factor : A → C^.obj)
    [factor_HasProduct : HasProduct C factor]
    : C^.obj
:= limit (ProductDrgm C factor)

/-! #brief Projection out of a product.
-/
definition product.π (C : Cat.{ℓobj ℓhom}) {A : Type ℓ}
    (factor : A → C^.obj)
    [factor_HasProduct : HasProduct C factor]
    (a : A)
    : C^.hom (product C factor) (factor a)
:= limit.out (ProductDrgm C factor) a

/-! #brief Every cone is mediated through the product.
-/
definition product.univ (C : Cat.{ℓobj ℓhom}) {A : Type ℓ}
    (factor : A → C^.obj)
    [factor_HasProduct : HasProduct C factor]
    (c : ProductCone C factor)
    : C^.hom c^.obj (product C factor)
:= limit.univ c

/-! #brief Every cone is mediated through the product.
-/
definition product.univ.mediates (C : Cat.{ℓobj ℓhom}) {A : Type ℓ}
    (factor : A → C^.obj)
    {factor_HasProduct : HasProduct C factor}
    (c : ProductCone C factor)
    (a : A)
    : c^.hom a = C^.circ (@product.π C A factor factor_HasProduct a) (product.univ C factor c)
:= limit.univ.mediates c a

/-! #brief The mediating map from the cone to the product is unique.
-/
definition product.univ.uniq (C : Cat.{ℓobj ℓhom}) {A : Type ℓ}
    (factor : A → C^.obj)
    {factor_HasProduct : HasProduct C factor}
    (c : ProductCone C factor)
    (m : C^.hom c^.obj (product C factor))
    (ω : ∀ (a : A), c^.hom a = (@product.π C A factor factor_HasProduct a) ∘∘ m)
    : m = product.univ C factor c
:= limit.univ.uniq c m ω

/-! #brief The unique iso between two products of the same factors.
-/
definition product.iso {C : Cat.{ℓobj ℓhom}} {A : Type ℓ}
    {factor : A → C^.obj}
    (factor_HasProduct₁ factor_HasProduct₂ : HasProduct C factor)
    : C^.hom (@product C A factor factor_HasProduct₁)
             (@product C A factor factor_HasProduct₂)
:= limit.iso factor_HasProduct₁ factor_HasProduct₂

/-! #brief Products are unique up-to unique isomorphism.
-/
definition product.uniq {C : Cat.{ℓobj ℓhom}} {A : Type ℓ}
    {factor : A → C^.obj}
    (factor_HasProduct₁ factor_HasProduct₂ : HasProduct C factor)
    : Iso (product.iso factor_HasProduct₁ factor_HasProduct₂)
          (product.iso factor_HasProduct₂ factor_HasProduct₁)
:= limit.uniq factor_HasProduct₁ factor_HasProduct₂



/- -----------------------------------------------------------------------
Finite products.
----------------------------------------------------------------------- -/

/-! #brief A cone over a finite product.
-/
definition FinProductCone (C : Cat.{ℓobj ℓhom})
    (factor : list C^.obj)
    : Type (max ℓobj ℓhom)
:= ProductCone C (list.get factor)

/-! #brief Projections out of a finite product cone.
-/
definition FinProductProj {C : Cat.{ℓobj ℓhom}}
    (c : C^.obj)
    (factor : list C^.obj)
    : Type (max ℓobj ℓhom)
:= dlist (C^.hom c) factor

/-! #brief Every finite product cone comes with projections.
-/
definition FinProductCone.Proj {C : Cat.{ℓobj ℓhom}}
    {factor : list C^.obj}
    (c : FinProductCone C factor)
    : FinProductProj c^.obj factor
:= dlist.enum (Cone.hom c)

/-! #brief Fetching a projection out of FinProductProj.
-/
definition FinProductProj.get {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor : list C^.obj}
    (proj : FinProductProj c factor)
    (n : fin (list.length factor))
    : C^.hom c (list.get factor n)
:= dlist.get proj n

/-! #brief An inverse to FinProductProj.get.
-/
definition FinProductProj.enum {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor : list C^.obj}
    (f : ∀ (n : fin (list.length factor)), C^.hom c (list.get factor n))
    : FinProductProj c factor
:= dlist.enum f

/-! #brief Helper for making a finite product cone.
-/
definition FinProductCone.mk {C : Cat.{ℓobj ℓhom}}
    {factor : list C^.obj}
    (c : C^.obj)
    (proj : FinProductProj c factor)
    : FinProductCone C factor
:= ProductCone.mk c (FinProductProj.get proj)

/-! #brief A finite product in a category.
-/
@[class] definition HasFinProduct (C : Cat.{ℓobj ℓhom})
    (factor : list C^.obj)
:= HasProduct C (list.get factor)

instance HasFinProduct.HasProduct (C : Cat.{ℓobj ℓhom})
    (factor : list C^.obj)
    [factor_HasProduct : HasFinProduct C factor]
    : HasProduct C (list.get factor)
:= factor_HasProduct

/-! #brief Helper for showing a category has a finite product.
-/
definition HasFinProduct.show {C : Cat.{ℓobj ℓhom}}
    {factor : list C^.obj}
    (p : C^.obj)
    (proj : FinProductProj p factor)
    (univ : ∀ (c : C^.obj) (hom : FinProductProj c factor)
            , C^.hom c p)
    (ωuniv : ∀ (c : C^.obj) (hom : FinProductProj c factor)
             , hom = dlist.map (λ a j, C^.circ j (univ c hom)) proj)
    (ωuniq : ∀ (c : C^.obj) (hom : FinProductProj c factor) (h : C^.hom c p)
               (ωcomm : hom = dlist.map (λ a j, C^.circ j h) proj)
             , h = univ c hom)
    : HasFinProduct C factor
:= HasProduct.show C p (FinProductProj.get proj)
    (λ c hom, univ c (FinProductProj.enum hom))
    (λ c hom n, let hom' : FinProductProj c factor := dlist.enum hom in
                let f := (λ a j, @Cat.circ C _ _ a j (univ c hom'))
                in begin
                     refine eq.trans (eq.symm (dlist.get_enum hom n)) _,
                     refine eq.trans _ (dlist.get_map f proj n),
                     exact congr_arg (λ bb, dlist.get bb n) (ωuniv c _)
                 end)
    (λ c hom h ωcomm, let hom' : FinProductProj c factor := dlist.enum hom in
                      let f := (λ a j, @Cat.circ C _ _ a j h)
                      in ωuniq c _ h (dlist.enum_eq_map f proj hom @ωcomm))

/-! #brief Finite products are cones.
-/
definition finproduct.cone (C : Cat.{ℓobj ℓhom})
    (factor : list C^.obj)
    [factor_HasFinProduct : HasFinProduct C factor]
    : FinProductCone C factor
:= product.cone C (list.get factor)

/-! #brief The product of a finite collection of objects.
-/
definition finproduct (C : Cat.{ℓobj ℓhom})
    (factor : list C^.obj)
    [factor_HasFinProduct : HasFinProduct C factor]
    : C^.obj
:= product C (list.get factor)

/-! #brief Projection out of a product.
-/
definition finproduct.π (C : Cat.{ℓobj ℓhom})
    (factor : list C^.obj)
    [factor_HasFinProduct : HasFinProduct C factor]
    (n : fin (list.length factor))
    : C^.hom (finproduct C factor) (list.get factor n)
:= product.π C (list.get factor) n

/-! #brief Every cone is mediated through the product.
-/
definition finproduct.univ (C : Cat.{ℓobj ℓhom})
    (factor : list C^.obj)
    [factor_HasFinProduct : HasFinProduct C factor]
    (c : FinProductCone C factor)
    : C^.hom c^.obj (finproduct C factor)
:= product.univ C (list.get factor) c

/-! #brief Every cone is mediated through the product.
-/
definition finproduct.univ.mediates (C : Cat.{ℓobj ℓhom})
    (factor : list C^.obj)
    [factor_HasFinProduct : HasFinProduct C factor]
    (c : FinProductCone C factor)
    (n : fin (list.length factor))
    : c^.hom n = C^.circ (@finproduct.π C factor factor_HasFinProduct n) (finproduct.univ C factor c)
:= product.univ.mediates C (list.get factor) c n

/-! #brief The mediating map from the cone to the product is unique.
-/
definition finproduct.univ.uniq (C : Cat.{ℓobj ℓhom})
    (factor : list C^.obj)
    [factor_HasFinProduct : HasFinProduct C factor]
    (c : FinProductCone C factor)
    (m : C^.hom c^.obj (finproduct C factor))
    (ω : c^.Proj = dlist.map (λ a j, C^.circ j m) (finproduct.cone C factor)^.Proj)
    : m = finproduct.univ C factor c
:= product.univ.uniq C (list.get factor) c m
    begin
      intro n,
      assert ω₁ : c^.hom n = dlist.get c^.Proj n,
      { apply eq.symm, apply dlist.get_enum },
      apply eq.trans ω₁,
      rw ω,
      rw dlist.get_map,
      apply congr_arg (λ j, C^.circ j m),
      apply dlist.get_enum
    end

/-! #brief The unique iso between two products of the same factors.
-/
definition finproduct.iso {C : Cat.{ℓobj ℓhom}}
    {factor : list C^.obj}
    (factor_HasFinProduct₁ factor_HasFinProduct₂ : HasFinProduct C factor)
    : C^.hom (@finproduct C factor factor_HasFinProduct₁)
             (@finproduct C factor factor_HasFinProduct₂)
:= product.iso factor_HasFinProduct₁ factor_HasFinProduct₂

/-! #brief Finite products are unique up-to unique isomorphism.
-/
definition finproduct.uniq {C : Cat.{ℓobj ℓhom}}
    {factor : list C^.obj}
    (factor_HasFinProduct₁ factor_HasFinProduct₂ : HasFinProduct C factor)
    : Iso (finproduct.iso factor_HasFinProduct₁ factor_HasFinProduct₂)
          (finproduct.iso factor_HasFinProduct₂ factor_HasFinProduct₁)
:= product.uniq factor_HasFinProduct₁ factor_HasFinProduct₂


end qp
