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

/-! #brief Composition with projections.
-/
definition FinProductProj.comp {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor : list C^.obj}
    (proj : FinProductProj c factor)
    {c' : C^.obj} (f : C^.hom c' c)
    : FinProductProj c' factor
:= dlist.map (λ a j, C^.circ j f) proj

/-! #brief Fetching a projection out of FinProductProj.
-/
definition FinProductProj.get {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor : list C^.obj}
    (proj : FinProductProj c factor)
    (n : fin (list.length factor))
    : C^.hom c (list.get factor n)
:= dlist.get proj n

/-! #brief get is injective.
-/
theorem FinProductProj.get.inj {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor : list C^.obj}
    (proj₁ proj₂ : FinProductProj c factor)
    (ω : FinProductProj.get proj₁ = FinProductProj.get proj₂)
    : proj₁ = proj₂
:= dlist.get.inj ω

/-! #brief get on comp.
-/
theorem FinProductProj.get_comp {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor : list C^.obj}
    {proj : FinProductProj c factor}
    {c' : C^.obj} {f : C^.hom c' c}
    {n : fin (list.length factor)}
    : FinProductProj.get (FinProductProj.comp proj f) n = C^.circ (FinProductProj.get proj n) f
:= dlist.get_map _ _ _

/-! #brief An inverse to FinProductProj.get.
-/
definition FinProductProj.enum {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor : list C^.obj}
    (f : ∀ (n : fin (list.length factor)), C^.hom c (list.get factor n))
    : FinProductProj c factor
:= dlist.enum f

/-! #brief enum and get are inverses.
-/
theorem FinProductProj.enum_get {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor : list C^.obj}
    (proj : FinProductProj c factor)
    : FinProductProj.enum (FinProductProj.get proj) = proj
:= dlist.enum_get

/-! #brief enum and get are inverses.
-/
theorem FinProductProj.get_enum {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor : list C^.obj}
    (f : ∀ (n : fin (list.length factor)), C^.hom c (list.get factor n))
    (n : fin (list.length factor))
    : FinProductProj.get (FinProductProj.enum f) n = f n
:= dlist.get_enum _ _

/-! #brief Appending lists of projections.
-/
definition FinProductProj.append {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor₁ factor₂ : list C^.obj}
    (proj₁ : FinProductProj c factor₁)
    (proj₂ : FinProductProj c factor₂)
    : FinProductProj c (factor₁ ++ factor₂)
:= dlist.append proj₁ proj₂

/-! #brief Splitting lists of projections.
-/
definition FinProductProj.split_left {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor₁ factor₂ : list C^.obj}
    (proj : FinProductProj c (factor₁ ++ factor₂))
    : FinProductProj c factor₁
:= dlist.split_left factor₁ proj

/-! #brief Splitting lists of projections.
-/
definition FinProductProj.split_right {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor₁ factor₂ : list C^.obj}
    (proj : FinProductProj c (factor₁ ++ factor₂))
    : FinProductProj c factor₂
:= dlist.split_right factor₁ proj

/-! #brief Equality of FinProductProj.append
-/
theorem FinProductProj.append_eq {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor₁ factor₂ : list C^.obj}
    (proj₁ proj₂ : FinProductProj c (factor₁ ++ factor₂))
    (ωleft : FinProductProj.split_left proj₁ = FinProductProj.split_left proj₂)
    (ωright : FinProductProj.split_right proj₁ = FinProductProj.split_right proj₂)
    : proj₁ = proj₂
:= dlist.append_eq ωleft ωright

/-! #brief Action of split_left on append.
-/
theorem FinProductProj.split_left_append {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor₁ factor₂ : list C^.obj}
    (proj₁ : FinProductProj c factor₁)
    (proj₂ : FinProductProj c factor₂)
    : FinProductProj.split_left (FinProductProj.append proj₁ proj₂)
       = proj₁
:= dlist.split_left_append

/-! #brief Action of split_right on append.
-/
theorem FinProductProj.split_right_append {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor₁ factor₂ : list C^.obj}
    (proj₁ : FinProductProj c factor₁)
    (proj₂ : FinProductProj c factor₂)
    : FinProductProj.split_right (FinProductProj.append proj₁ proj₂)
       = proj₂
:= dlist.split_right_append

/-! #brief Action of split_left on comp.
-/
theorem FinProductProj.split_left_comp {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor₁ factor₂ : list C^.obj}
    (proj : FinProductProj c (factor₁ ++ factor₂))
    {c' : C^.obj} (f : C^.hom c' c)
    : FinProductProj.split_left (FinProductProj.comp proj f)
       = FinProductProj.comp (FinProductProj.split_left proj) f
:= dlist.split_left_map _

/-! #brief Action of split_right on comp.
-/
theorem FinProductProj.split_right_comp {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor₁ factor₂ : list C^.obj}
    (proj : FinProductProj c (factor₁ ++ factor₂))
    {c' : C^.obj} (f : C^.hom c' c)
    : FinProductProj.split_right (FinProductProj.comp proj f)
       = FinProductProj.comp (FinProductProj.split_right proj) f
:= dlist.split_right_map _

/-! #brief Action of get on an append.
-/
theorem FinProductProj.get_append {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor₁ factor₂ : list C^.obj}
    (proj₁ : FinProductProj c factor₁)
    (proj₂ : FinProductProj c factor₂)
    (n : ℕ) (ωn : n < list.length factor₁)
    : FinProductProj.get (FinProductProj.append proj₁ proj₂) (fin.mk n (list.length.grow_left ωn))
       == FinProductProj.get proj₁ (fin.mk n ωn)
:= dlist.get_append

/-! #brief Action of get on split_left.
-/
theorem FinProductProj.get_split_left {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor₁ factor₂ : list C^.obj}
    {proj : FinProductProj c (factor₁ ++ factor₂)}
    {n : ℕ} {ωn : n < list.length factor₁}
    : FinProductProj.get (FinProductProj.split_left proj) (fin.mk n ωn)
       = cast_hom list.get_append_left
          ∘∘ FinProductProj.get proj (fin.mk n (list.length.grow_left ωn))
:= begin
     apply eq_of_heq,
     refine heq.trans _ (heq.symm (cast_hom.circ_left_heq _ _)),
     apply dlist.get_split_left
   end

/-! #brief Action of get on split_right.
-/
theorem FinProductProj.get_split_right {C : Cat.{ℓobj ℓhom}} {c : C^.obj}
    {factor₁ factor₂ : list C^.obj}
    {proj : FinProductProj c (factor₁ ++ factor₂)}
    {n : ℕ} {ωn : n < list.length factor₂}
    : FinProductProj.get (FinProductProj.split_right proj) (fin.mk n ωn)
       = cast_hom list.get_append_right
          ∘∘ FinProductProj.get proj (fin.mk (n + list.length factor₁) (list.length.grow_right ωn))
:= begin
     apply eq_of_heq,
     refine heq.trans _ (heq.symm (cast_hom.circ_left_heq _ _)),
     apply dlist.get_split_right
   end

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
             , hom = FinProductProj.comp proj (univ c hom))
    (ωuniq : ∀ (c : C^.obj) (hom : FinProductProj c factor) (h : C^.hom c p)
               (ωcomm : hom = FinProductProj.comp proj h)
             , h = univ c hom)
    : HasFinProduct C factor
:= HasProduct.show C p (FinProductProj.get proj)
    (λ c hom, univ c (FinProductProj.enum hom))
    (λ c hom n, let hom' : FinProductProj c factor := FinProductProj.enum hom in
                let f := (λ a j, @Cat.circ C _ _ a j (univ c hom'))
                in begin
                     refine eq.trans (eq.symm (dlist.get_enum hom n)) _,
                     refine eq.trans _ (dlist.get_map f proj n),
                     exact congr_arg (λ bb, FinProductProj.get bb n) (ωuniv c _)
                 end)
    (λ c hom h ωcomm, let hom' : FinProductProj c factor := FinProductProj.enum hom in
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
    {c : C^.obj} (hom : FinProductProj c factor)
    : C^.hom c (finproduct C factor)
:= product.univ C (list.get factor) (FinProductCone.mk c hom)

/-! #brief Every cone is mediated through the product.
-/
definition finproduct.univ.mediates (C : Cat.{ℓobj ℓhom})
    (factor : list C^.obj)
    [factor_HasFinProduct : HasFinProduct C factor]
    {c : C^.obj} (hom : FinProductProj c factor)
    (n : fin (list.length factor))
    : FinProductProj.get hom n = C^.circ (finproduct.π C factor n) (finproduct.univ C factor hom)
:= product.univ.mediates C (list.get factor) (FinProductCone.mk c hom) n

/-! #brief The mediating map from the cone to the product is unique.
-/
definition finproduct.univ.uniq (C : Cat.{ℓobj ℓhom})
    (factor : list C^.obj)
    [factor_HasFinProduct : HasFinProduct C factor]
    {c : C^.obj} (hom : FinProductProj c factor)
    (m : C^.hom c (finproduct C factor))
    (ω : hom = FinProductProj.comp (finproduct.cone C factor)^.Proj m)
    : m = finproduct.univ C factor hom
:= product.univ.uniq C (list.get factor) (FinProductCone.mk c hom) m
    begin
      intro n,
      rw ω,
      refine eq.trans (dlist.get_map _ _ n) _,
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



/- -----------------------------------------------------------------------
Isos between finite products.
----------------------------------------------------------------------- -/

/-! #brief Singleton products are trivial.
-/
definition HasFinProduct.singleton {C : Cat.{ℓobj ℓhom}}
    (c : C^.obj)
    : HasFinProduct C [c]
:= HasFinProduct.show c
    (dlist.cons c (C^.id c) [] (dlist.nil _))
    (λ c' proj, begin cases proj, exact b end)
    (λ c' hom, begin
                 cases hom, apply dlist.eq,
                 { exact eq.symm C^.circ_id_left },
                 cases bb, trivial
               end)
    (λ c' hom h ωh, begin cases hom, cases ωh, exact eq.symm C^.circ_id_left end)

definition finproduct.singleton.un {C : Cat.{ℓobj ℓhom}}
    (c : C^.obj)
    [c_HasFinProduct : HasFinProduct C [c]]
    : C^.hom (finproduct C [c]) c
:= finproduct.iso c_HasFinProduct (HasFinProduct.singleton c)

definition finproduct.singleton.to {C : Cat.{ℓobj ℓhom}}
    (c : C^.obj)
    [c_HasFinProduct : HasFinProduct C [c]]
    : C^.hom c (finproduct C [c])
:= finproduct.iso (HasFinProduct.singleton c) c_HasFinProduct

definition finproduct.singleton.Iso {C : Cat.{ℓobj ℓhom}}
    (c : C^.obj)
    [c_HasFinProduct : HasFinProduct C [c]]
    : Iso  (finproduct.singleton.to c) (finproduct.singleton.un c)
:= finproduct.uniq (HasFinProduct.singleton c) c_HasFinProduct



/-! #brief Projections for the flattened product.
-/
definition HasFinProduct.flatten.Proj {C : Cat.{ℓobj ℓhom}}
    (factor₁ factor₂ factor₃ : list C^.obj)
    [factor₂_HasFinProduct : HasFinProduct C factor₂]
    [factor₁₂₃_HasFinProduct : HasFinProduct C (factor₁ ++ [finproduct C factor₂] ++ factor₃)]
    : FinProductProj (finproduct C (factor₁ ++ [finproduct C factor₂] ++ factor₃))
                     (factor₁ ++ factor₂ ++ factor₃)
:= let prj₁₂₃ : FinProductProj (finproduct C (factor₁ ++ [finproduct C factor₂] ++ factor₃))
                              (factor₁ ++ [finproduct C factor₂] ++ factor₃)
           := (@finproduct.cone _ _ factor₁₂₃_HasFinProduct)^.Proj in
   let f₁ : FinProductProj (finproduct C (factor₁ ++ [finproduct C factor₂] ++ factor₃)) factor₁
         := FinProductProj.split_left (FinProductProj.split_left prj₁₂₃) in
   let f₂ : FinProductProj (finproduct C (factor₁ ++ [finproduct C factor₂] ++ factor₃)) [finproduct C factor₂]
         := FinProductProj.split_right (FinProductProj.split_left prj₁₂₃) in
   let f₂' := FinProductProj.comp (@finproduct.cone _ _ factor₂_HasFinProduct)^.Proj (dlist.head f₂) in
   let f₃ : FinProductProj (finproduct C (factor₁ ++ [finproduct C factor₂] ++ factor₃)) factor₃
         := FinProductProj.split_right prj₁₂₃
   in FinProductProj.append (FinProductProj.append f₁ f₂') f₃

/-! #brief The projections used by the universal map for the flattened product.
-/
definition HasFinProduct.flatten.univ.Proj {C : Cat.{ℓobj ℓhom}}
    (factor₁ factor₂ factor₃ : list C^.obj)
    [factor₂_HasFinProduct : HasFinProduct C factor₂]
    [factor₁₂₃_HasFinProduct : HasFinProduct C (factor₁ ++ [finproduct C factor₂] ++ factor₃)]
    (c : C^.obj)
    (hom : FinProductProj c (factor₁ ++ factor₂ ++ factor₃))
    : FinProductProj c (factor₁ ++ [finproduct C factor₂] ++ factor₃)
:= let f₁ : FinProductProj c factor₁
         := FinProductProj.split_left (FinProductProj.split_left hom) in
   let f₂ : FinProductProj c [finproduct C factor₂]
         := dlist.cons _
               (finproduct.univ C factor₂
                 (FinProductProj.split_right (FinProductProj.split_left hom)))
               _ (dlist.nil _) in
   let f₃ : FinProductProj c factor₃
         := FinProductProj.split_right hom
   in FinProductProj.append (FinProductProj.append f₁ f₂) f₃

/-! #brief Universal map for the flattened product.
-/
definition HasFinProduct.flatten.univ {C : Cat.{ℓobj ℓhom}}
    (factor₁ factor₂ factor₃ : list C^.obj)
    [factor₂_HasFinProduct : HasFinProduct C factor₂]
    [factor₁₂₃_HasFinProduct : HasFinProduct C (factor₁ ++ [finproduct C factor₂] ++ factor₃)]
    (c : C^.obj)
    (hom : FinProductProj c (factor₁ ++ factor₂ ++ factor₃))
    : C^.hom c (finproduct C (factor₁ ++ [finproduct C factor₂] ++ factor₃))
:= finproduct.univ C (factor₁ ++ [finproduct C factor₂] ++ factor₃)
                     (HasFinProduct.flatten.univ.Proj factor₁ factor₂ factor₃ c hom)


/-! #brief Flattening of products.
-/
definition HasFinProduct.flatten {C : Cat.{ℓobj ℓhom}}
    (factor₁ factor₂ factor₃ : list C^.obj)
    [factor₂_HasFinProduct : HasFinProduct C factor₂]
    [factor₁₂₃_HasFinProduct : HasFinProduct C (factor₁ ++ [finproduct C factor₂] ++ factor₃)]
    : HasFinProduct C (factor₁ ++ factor₂ ++ factor₃)
:= HasFinProduct.show
    (finproduct C (factor₁ ++ [finproduct C factor₂] ++ factor₃))
    (HasFinProduct.flatten.Proj factor₁ factor₂ factor₃)
    (HasFinProduct.flatten.univ factor₁ factor₂ factor₃)
    begin
      intros c hom,
      apply FinProductProj.append_eq,
      apply FinProductProj.append_eq,
      { repeat { rw FinProductProj.split_left_comp },
        unfold HasFinProduct.flatten.Proj,
        repeat { rw FinProductProj.split_left_append },
        apply FinProductProj.get.inj,
        apply funext, intro n, cases n with n ωn,
        rw FinProductProj.get_comp,
        repeat { rw FinProductProj.get_split_left },
        repeat { rw C^.circ_assoc },
        repeat { rw cast_hom.circ },
        rw -C^.circ_assoc,
        apply cast_hom.circ.congr_right,
        unfold HasFinProduct.flatten.univ,
        refine heq.trans _ (heq_of_eq (Cat.circ.congr_left (eq.symm (FinProductProj.get_enum _ _)))),
        refine heq.trans _ (heq_of_eq (finproduct.univ.mediates C
                                        (factor₁ ++ [finproduct C factor₂] ++ factor₃)
                                        (HasFinProduct.flatten.univ.Proj factor₁ factor₂ factor₃ c hom)
                                        {val := n, is_lt := list.length.grow_left (list.length.grow_left ωn)})),
        unfold HasFinProduct.flatten.univ.Proj,
        refine heq.trans _ (heq.symm (FinProductProj.get_append _ _ _ _)),
        refine heq.trans _ (heq.symm (FinProductProj.get_append _ _ _ _)),
        repeat { rw FinProductProj.get_split_left },
        rw [C^.circ_assoc, cast_hom.circ],
        refine heq.trans _ (heq.symm (cast_hom.circ_left_heq _ _)),
        apply heq.refl
      },
      { exact sorry 
      },
      { exact sorry
      }
    end
    begin
      intros c hom h ωh,
      exact sorry
    end

definition finproduct.unflatten {C : Cat.{ℓobj ℓhom}}
    (factor₁ factor₂ factor₃ : list C^.obj)
    [factor₂_HasFinProduct : HasFinProduct C factor₂]
    [factor₁₂₃_HasFinProduct : HasFinProduct C (factor₁ ++ [finproduct C factor₂] ++ factor₃)]
    [factor₁₂₃_flat_HasFinProduct : HasFinProduct C (factor₁ ++ factor₂ ++ factor₃)]
    : C^.hom (finproduct C (factor₁ ++ factor₂ ++ factor₃))
             (finproduct C (factor₁ ++ [finproduct C factor₂] ++ factor₃))
:= finproduct.iso factor₁₂₃_flat_HasFinProduct (HasFinProduct.flatten factor₁ factor₂ factor₃)

definition finproduct.flatten {C : Cat.{ℓobj ℓhom}}
    (factor₁ factor₂ factor₃ : list C^.obj)
    [factor₂_HasFinProduct : HasFinProduct C factor₂]
    [factor₁₂₃_HasFinProduct : HasFinProduct C (factor₁ ++ [finproduct C factor₂] ++ factor₃)]
    [factor₁₂₃_flat_HasFinProduct : HasFinProduct C (factor₁ ++ factor₂ ++ factor₃)]
    : C^.hom (finproduct C (factor₁ ++ [finproduct C factor₂] ++ factor₃))
             (finproduct C (factor₁ ++ factor₂ ++ factor₃))
:= finproduct.iso (HasFinProduct.flatten factor₁ factor₂ factor₃) factor₁₂₃_flat_HasFinProduct

definition finproduct.flatten.Iso {C : Cat.{ℓobj ℓhom}}
    (factor₁ factor₂ factor₃ : list C^.obj)
    [factor₂_HasFinProduct : HasFinProduct C factor₂]
    [factor₁₂₃_HasFinProduct : HasFinProduct C (factor₁ ++ [finproduct C factor₂] ++ factor₃)]
    [factor₁₂₃_flat_HasFinProduct : HasFinProduct C (factor₁ ++ factor₂ ++ factor₃)]
    : Iso  (finproduct.flatten factor₁ factor₂ factor₃)
           (finproduct.unflatten factor₁ factor₂ factor₃)
:= finproduct.uniq (HasFinProduct.flatten factor₁ factor₂ factor₃) factor₁₂₃_flat_HasFinProduct

end qp
