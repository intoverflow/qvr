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

/-! #brief The product diagram turns heterogeneous equality into natural isomorphisms.
-/
definition ProductDrgm.heq (C : Cat.{ℓobj ℓhom})
    : ∀ {A₁ A₂ : Type ℓ} (ωA : A₁ = A₂)
        {factor₁ : A₁ → C^.obj} {factor₂ : A₂ → C^.obj}
        (ωfactor : factor₁ == factor₂)
      , ProductDrgm C factor₁ == ProductDrgm C factor₂
| A .(A) (eq.refl .(A)) factor .(factor) (heq.refl .(factor)) := heq.refl _

/-! #brief A handy identity.
-/
theorem ProductDrgm.on_Fun {C : Cat.{ℓobj ℓhom}} {A : Type ℓ}
    (F : Fun (ObjCat A) C)
    : ProductDrgm C F^.obj = F
:= Fun.eq (λ x, rfl)
    (λ ω x y f
     , begin
         dsimp [ObjCat, PreorderCat] at f,
         subst f,
         apply heq_of_eq,
         apply eq.symm,
         apply F^.hom_id
       end)

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

/-! #brief A category with all products.
-/
class HasAllProducts (C : Cat.{ℓobj ℓhom})
:= (has_product : ∀ {A : Type ℓ} (factor : A → C^.obj)
                  , HasProduct C factor)

instance HasAllProducts.HasProduct (C : Cat.{ℓobj ℓhom})
    [C_HasAllProducts : HasAllProducts.{ℓ} C]
    {A : Type ℓ} (factor : A → C^.obj)
    : HasProduct C factor
:= HasAllProducts.has_product factor

instance HasAllProducts.HasAllLimitsFrom.ObjCat (C : Cat.{ℓobj ℓhom})
    [C_HasAllProducts : HasAllProducts.{ℓ} C]
    (A : Type ℓ)
    : HasAllLimitsFrom C (ObjCat A)
:= { has_limit := λ L, let l := HasAllProducts.HasProduct C L^.obj
                       in cast (congr_arg HasLimit (ProductDrgm.on_Fun L)) l
   }

/-! #brief Helper for showing a category has a product.
-/
definition HasProduct.show (C : Cat.{ℓobj ℓhom}) {A : Type ℓ}
    (factor : A → C^.obj)
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
:= limit.univ _ c

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
Products in functor categories.
----------------------------------------------------------------------- -/

/-! #brief Products in functor categories can be computed pointwise.
-/
instance FunCat.HasProduct {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    [D_HasAllProducts : HasAllProducts.{ℓ} D]
    {A : Type ℓ} (factor : A → Fun C D)
    : HasProduct (FunCat C D) factor
:= FunCat.HasLimit (ProductDrgm _ factor)

/-! #brief Products in functor categories can be computed pointwise.
-/
instance FunCat.HasAllProducts {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    [D_HasAllProducts : HasAllProducts.{ℓ} D]
    : HasAllProducts.{ℓ} (FunCat C D)
:= { has_product := λ A factor, FunCat.HasProduct factor
   }



/- -----------------------------------------------------------------------
Finite products.
----------------------------------------------------------------------- -/

/-! #brief A cone over a finite product.
-/
definition FinProductCone (C : Cat.{ℓobj ℓhom})
    (factor : list C^.obj)
    : Type (max ℓobj ℓhom)
:= ProductCone C (list.get factor)

/-! #brief Every finite product cone comes with projections.
-/
definition FinProductCone.Proj {C : Cat.{ℓobj ℓhom}}
    {factor : list C^.obj}
    (c : FinProductCone C factor)
    : HomsOut c^.obj factor
:= dlist.enum (Cone.hom c)

/-! #brief Helper for making a finite product cone.
-/
definition FinProductCone.mk {C : Cat.{ℓobj ℓhom}}
    {factor : list C^.obj}
    (c : C^.obj)
    (proj : HomsOut c factor)
    : FinProductCone C factor
:= ProductCone.mk c (HomsOut.get proj)

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

/-! #brief A category with all finite products.
-/
class HasAllFinProducts (C : Cat.{ℓobj ℓhom})
:= (has_product : ∀ (factor : list C^.obj), HasFinProduct C factor)

instance HasAllFinProducts.HasFinProduct (C : Cat.{ℓobj ℓhom})
    [C_HasAllFinProducts : HasAllFinProducts C]
    (factor : list C^.obj)
    : HasFinProduct C factor
:= HasAllFinProducts.has_product factor

instance HasAllFinProducts.HasAllLimitsFrom.ObjCat (C : Cat.{ℓobj ℓhom})
    [C_HasAllFinProducts : HasAllFinProducts C]
    (N : ℕ)
    : HasAllLimitsFrom C (ObjCat (fin N))
:= { has_limit
      := λ L, let l := HasAllFinProducts.HasFinProduct C (fin.enum L^.obj)
           in let ω₁ : ObjCat (fin (list.length (fin.enum (L^.obj)))) = ObjCat (fin N)
                    := by rw list.length_enum
           in let ω₂ : ProductDrgm C (list.get (fin.enum L^.obj)) == L
                   := by calc ProductDrgm C (list.get (fin.enum L^.obj))
                                  == ProductDrgm C L^.obj : ProductDrgm.heq _ (congr_arg fin (list.length_enum _))
                                                             list.get_enum'
                              ... = L                     : ProductDrgm.on_Fun L
              in cast (HasLimit.heq (by rw list.length_enum) rfl ω₂) l
   }

/-! #brief Helper for showing a category has a finite product.
-/
definition HasFinProduct.show {C : Cat.{ℓobj ℓhom}}
    (factor : list C^.obj)
    (p : C^.obj)
    (proj : HomsOut p factor)
    (univ : ∀ (c : C^.obj) (hom : HomsOut c factor)
            , C^.hom c p)
    (ωuniv : ∀ (c : C^.obj) (hom : HomsOut c factor)
             , hom = HomsOut.comp proj (univ c hom))
    (ωuniq : ∀ (c : C^.obj) (hom : HomsOut c factor) (h : C^.hom c p)
               (ωcomm : hom = HomsOut.comp proj h)
             , h = univ c hom)
    : HasFinProduct C factor
:= HasProduct.show C _ p (HomsOut.get proj)
    (λ c hom, univ c (HomsOut.enum hom))
    (λ c hom n, let hom' : HomsOut c factor := HomsOut.enum hom in
                let f := (λ a j, @Cat.circ C _ _ a j (univ c hom'))
                in begin
                     refine eq.trans (eq.symm (dlist.get_enum hom n)) _,
                     refine eq.trans _ (dlist.get_map f proj n),
                     exact congr_arg (λ bb, HomsOut.get bb n) (ωuniv c _)
                 end)
    (λ c hom h ωcomm, let hom' : HomsOut c factor := HomsOut.enum hom in
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
:= (finproduct.cone C factor)^.obj

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
    {c : C^.obj} (hom : HomsOut c factor)
    : C^.hom c (finproduct C factor)
:= product.univ C (list.get factor) (FinProductCone.mk c hom)

/-! #brief Every cone is mediated through the product.
-/
definition finproduct.univ.mediates (C : Cat.{ℓobj ℓhom})
    (factor : list C^.obj)
    [factor_HasFinProduct : HasFinProduct C factor]
    {c : C^.obj} (hom : HomsOut c factor)
    (n : fin (list.length factor))
    : HomsOut.get hom n = C^.circ (finproduct.π C factor n) (finproduct.univ C factor hom)
:= product.univ.mediates C (list.get factor) (FinProductCone.mk c hom) n

/-! #brief The mediating map from the cone to the product is unique.
-/
definition finproduct.univ.uniq (C : Cat.{ℓobj ℓhom})
    (factor : list C^.obj)
    [factor_HasFinProduct : HasFinProduct C factor]
    {c : C^.obj} (hom : HomsOut c factor)
    (m : C^.hom c (finproduct C factor))
    (ω : hom = HomsOut.comp (finproduct.cone C factor)^.Proj m)
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
Finite products in functor categories.
----------------------------------------------------------------------- -/

/-! #brief Finite products in functor categories can be computed pointwise.
-/
definition FunCat.HasFinProduct {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    [D_HasAllFinProducts : HasAllFinProducts D]
    (factor : list (Fun C D))
    : HasFinProduct (FunCat C D) factor
:= FunCat.HasLimit (ProductDrgm _ (list.get factor))

/-! #brief Finite products in functor categories can be computed pointwise.
-/
instance FunCat.HasAllFinProducts {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    [D_HasAllFinProducts : HasAllFinProducts D]
    : HasAllFinProducts (FunCat C D)
:= { has_product := λ factor, FunCat.HasFinProduct factor
   }



/- -----------------------------------------------------------------------
Finite products of homs.
----------------------------------------------------------------------- -/

/-! #brief The product of a list of homs.
-/
definition finproduct.hom {C : Cat.{ℓobj ℓhom}}
    {ccs : list (prod C^.obj C^.obj)}
    (fns : HomsList C ccs)
    [ccs_domFinProduct : HasFinProduct C (list.map prod.fst ccs)]
    [ccs_codomFinProduct : HasFinProduct C (list.map prod.snd ccs)]
    : C^.hom (finproduct C (list.map prod.fst ccs))
             (finproduct C (list.map prod.snd ccs))
:= finproduct.univ _ _ (homs_comp_out fns (finproduct.cone C (list.map prod.fst ccs))^.Proj)

example (C : Cat) {x₁ x₂ y₁ y₂ : ⟦C⟧}
        [x_HasFinProduct : HasFinProduct C [x₁, x₂] ]
        [y_HasFinProduct : HasFinProduct C [y₁, y₂] ]
        (f₁ : ⟦C: x₁ →→ y₁⟧)
        (f₂ : ⟦C: x₂ →→ y₂⟧)
        : ⟦C: finproduct C [x₁, x₂] →→ finproduct C [y₁, y₂] ⟧
:= finproduct.hom (f₁ ↗ f₂ ↗↗)

theorem finproduct.hom₂.id {C : Cat} {x₁ x₂ : ⟦C⟧}
        [x_HasFinProduct : HasFinProduct C [x₁, x₂] ]
        : @finproduct.hom _ _ (⟨⟨x₁⟩⟩ ↗ ⟨⟨x₂⟩⟩ ↗↗) x_HasFinProduct x_HasFinProduct
            = C^.id (finproduct C [x₁, x₂])
:= sorry

theorem finproduct.hom₂.circ {C : Cat} {x₁ x₂ y₁ y₂ z₁ z₂ : ⟦C⟧}
        [x_HasFinProduct : HasFinProduct C [x₁, x₂] ]
        [y_HasFinProduct : HasFinProduct C [y₁, y₂] ]
        [z_HasFinProduct : HasFinProduct C [z₁, z₂] ]
        (g₁ : C^.hom y₁ z₁) (g₂ : C^.hom y₂ z₂)
        (f₁ : C^.hom x₁ y₁) (f₂ : C^.hom x₂ y₂)
        : @finproduct.hom _ _ ((g₁ ∘∘ f₁) ↗ (g₂ ∘∘ f₂) ↗↗) x_HasFinProduct z_HasFinProduct
           = @finproduct.hom _ _ (g₁ ↗ g₂ ↗↗) y_HasFinProduct z_HasFinProduct
              ∘∘ @finproduct.hom _ _ (f₁ ↗ f₂ ↗↗) x_HasFinProduct y_HasFinProduct
:= sorry



/- -----------------------------------------------------------------------
Isos between finite products.
----------------------------------------------------------------------- -/

/-! #brief Singleton products are trivial.
-/
instance HasFinProduct.singleton {C : Cat.{ℓobj ℓhom}}
    (c : C^.obj)
    : HasFinProduct C [c]
:= HasFinProduct.show _ c
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



/-! #brief Projections for the (right) flattened product.
-/
definition HasFinProduct.flatten_right.Proj {C : Cat.{ℓobj ℓhom}}
    (factor₁ factor₂ : list C^.obj)
    [factor₂_HasFinProduct : HasFinProduct C factor₂]
    [factor₁₂_HasFinProduct : HasFinProduct C (factor₁ ++ [finproduct C factor₂])]
    : HomsOut (finproduct C (factor₁ ++ [finproduct C factor₂]))
                     (factor₁ ++ factor₂)
:= let prj₁₂ : HomsOut (finproduct C (factor₁ ++ [finproduct C factor₂]))
                       (factor₁ ++ [finproduct C factor₂])
           := (@finproduct.cone _ _ factor₁₂_HasFinProduct)^.Proj in
   let f₁ : HomsOut (finproduct C (factor₁ ++ [finproduct C factor₂])) factor₁
         := HomsOut.split_left prj₁₂ in
   let f₂ : HomsOut (finproduct C (factor₁ ++ [finproduct C factor₂])) [finproduct C factor₂]
         := HomsOut.split_right prj₁₂ in
   let f₂' := HomsOut.comp (@finproduct.cone _ _ factor₂_HasFinProduct)^.Proj (HomsOut.get f₂ fin.zero)
   in HomsOut.append f₁ f₂'

/-! #brief The projections used by the universal map for the (right) flattened product.
-/
definition HasFinProduct.flatten_right.univ.Proj {C : Cat.{ℓobj ℓhom}}
    (factor₁ factor₂ : list C^.obj)
    [factor₂_HasFinProduct : HasFinProduct C factor₂]
    [factor₁₂_HasFinProduct : HasFinProduct C (factor₁ ++ [finproduct C factor₂])]
    (c : C^.obj)
    (homs : HomsOut c (factor₁ ++ factor₂))
    : HomsOut c (factor₁ ++ [finproduct C factor₂])
:= let f₁ : HomsOut c factor₁
         := HomsOut.split_left homs in
   let f₂ : HomsOut c [finproduct C factor₂]
         := dlist.cons _
               (finproduct.univ C factor₂
                 (HomsOut.split_right homs))
               _ (dlist.nil _)
   in HomsOut.append f₁ f₂

/-! #brief Universal map for the (right) flattened product.
-/
definition HasFinProduct.flatten_right.univ {C : Cat.{ℓobj ℓhom}}
    (factor₁ factor₂ : list C^.obj)
    [factor₂_HasFinProduct : HasFinProduct C factor₂]
    [factor₁₂_HasFinProduct : HasFinProduct C (factor₁ ++ [finproduct C factor₂])]
    (c : C^.obj)
    (hom : HomsOut c (factor₁ ++ factor₂))
    : C^.hom c (finproduct C (factor₁ ++ [finproduct C factor₂]))
:= finproduct.univ C (factor₁ ++ [finproduct C factor₂])
                     (HasFinProduct.flatten_right.univ.Proj factor₁ factor₂ c hom)

/-! #brief Flattening of products on the right.
-/
definition HasFinProduct.flatten_right {C : Cat.{ℓobj ℓhom}}
    (factor₁ factor₂ : list C^.obj)
    [factor₂_HasFinProduct : HasFinProduct C factor₂]
    [factor₁₂_HasFinProduct : HasFinProduct C (factor₁ ++ [finproduct C factor₂])]
    : HasFinProduct C (factor₁ ++ factor₂)
:= HasFinProduct.show _
    (finproduct C (factor₁ ++ [finproduct C factor₂]))
    (HasFinProduct.flatten_right.Proj factor₁ factor₂)
    (HasFinProduct.flatten_right.univ factor₁ factor₂)
    sorry
    sorry

definition finproduct.flatten_right {C : Cat.{ℓobj ℓhom}}
    (factor₁ factor₂ : list C^.obj)
    [factor₂_HasFinProduct : HasFinProduct C factor₂]
    [factor₁₂_HasFinProduct : HasFinProduct C (factor₁ ++ [finproduct C factor₂])]
    [factor₁₂_flat_HasFinProduct : HasFinProduct C (factor₁ ++ factor₂)]
    : C^.hom (finproduct C (factor₁ ++ [finproduct C factor₂]))
             (finproduct C (factor₁ ++ factor₂))
:= finproduct.iso (HasFinProduct.flatten_right factor₁ factor₂) factor₁₂_flat_HasFinProduct

definition finproduct.unflatten_right {C : Cat.{ℓobj ℓhom}}
    (factor₁ factor₂ : list C^.obj)
    [factor₂_HasFinProduct : HasFinProduct C factor₂]
    [factor₁₂_HasFinProduct : HasFinProduct C (factor₁ ++ [finproduct C factor₂])]
    [factor₁₂_flat_HasFinProduct : HasFinProduct C (factor₁ ++ factor₂)]
    : C^.hom (finproduct C (factor₁ ++ factor₂))
             (finproduct C (factor₁ ++ [finproduct C factor₂]))
:= finproduct.iso factor₁₂_flat_HasFinProduct (HasFinProduct.flatten_right factor₁ factor₂)

definition finproduct.flatten_right.Iso {C : Cat.{ℓobj ℓhom}}
    (factor₁ factor₂ : list C^.obj)
    [factor₂_HasFinProduct : HasFinProduct C factor₂]
    [factor₁₂_HasFinProduct : HasFinProduct C (factor₁ ++ [finproduct C factor₂])]
    [factor₁₂_flat_HasFinProduct : HasFinProduct C (factor₁ ++ factor₂)]
    : Iso  (finproduct.flatten_right factor₁ factor₂)
           (finproduct.unflatten_right factor₁ factor₂)
:= finproduct.uniq (HasFinProduct.flatten_right factor₁ factor₂) factor₁₂_flat_HasFinProduct



/-! #brief Projections for the flattened product.
-/
definition HasFinProduct.flatten.Proj {C : Cat.{ℓobj ℓhom}}
    (factor₁ factor₂ factor₃ : list C^.obj)
    [factor₂_HasFinProduct : HasFinProduct C factor₂]
    [factor₁₂₃_HasFinProduct : HasFinProduct C (factor₁ ++ [finproduct C factor₂] ++ factor₃)]
    : HomsOut (finproduct C (factor₁ ++ [finproduct C factor₂] ++ factor₃))
                     (factor₁ ++ factor₂ ++ factor₃)
:= let prj₁₂₃ : HomsOut (finproduct C (factor₁ ++ [finproduct C factor₂] ++ factor₃))
                              (factor₁ ++ [finproduct C factor₂] ++ factor₃)
           := (@finproduct.cone _ _ factor₁₂₃_HasFinProduct)^.Proj in
   let f₁ : HomsOut (finproduct C (factor₁ ++ [finproduct C factor₂] ++ factor₃)) factor₁
         := HomsOut.split_left (HomsOut.split_left prj₁₂₃) in
   let f₂ : HomsOut (finproduct C (factor₁ ++ [finproduct C factor₂] ++ factor₃)) [finproduct C factor₂]
         := HomsOut.split_right (HomsOut.split_left prj₁₂₃) in
   let f₂' := HomsOut.comp (@finproduct.cone _ _ factor₂_HasFinProduct)^.Proj (HomsOut.get f₂ fin.zero) in
   let f₃ : HomsOut (finproduct C (factor₁ ++ [finproduct C factor₂] ++ factor₃)) factor₃
         := HomsOut.split_right prj₁₂₃
   in HomsOut.append (HomsOut.append f₁ f₂') f₃

/-! #brief The projections used by the universal map for the flattened product.
-/
definition HasFinProduct.flatten.univ.Proj {C : Cat.{ℓobj ℓhom}}
    (factor₁ factor₂ factor₃ : list C^.obj)
    [factor₂_HasFinProduct : HasFinProduct C factor₂]
    [factor₁₂₃_HasFinProduct : HasFinProduct C (factor₁ ++ [finproduct C factor₂] ++ factor₃)]
    (c : C^.obj)
    (hom : HomsOut c (factor₁ ++ factor₂ ++ factor₃))
    : HomsOut c (factor₁ ++ [finproduct C factor₂] ++ factor₃)
:= let f₁ : HomsOut c factor₁
         := HomsOut.split_left (HomsOut.split_left hom) in
   let f₂ : HomsOut c [finproduct C factor₂]
         := dlist.cons _
               (finproduct.univ C factor₂
                 (HomsOut.split_right (HomsOut.split_left hom)))
               _ (dlist.nil _) in
   let f₃ : HomsOut c factor₃
         := HomsOut.split_right hom
   in HomsOut.append (HomsOut.append f₁ f₂) f₃

/-! #brief Universal map for the flattened product.
-/
definition HasFinProduct.flatten.univ {C : Cat.{ℓobj ℓhom}}
    (factor₁ factor₂ factor₃ : list C^.obj)
    [factor₂_HasFinProduct : HasFinProduct C factor₂]
    [factor₁₂₃_HasFinProduct : HasFinProduct C (factor₁ ++ [finproduct C factor₂] ++ factor₃)]
    (c : C^.obj)
    (hom : HomsOut c (factor₁ ++ factor₂ ++ factor₃))
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
:= HasFinProduct.show _
    (finproduct C (factor₁ ++ [finproduct C factor₂] ++ factor₃))
    (HasFinProduct.flatten.Proj factor₁ factor₂ factor₃)
    (HasFinProduct.flatten.univ factor₁ factor₂ factor₃)
    begin
      intros c hom,
      apply HomsOut.append_eq,
      apply HomsOut.append_eq,
      { repeat { rw HomsOut.split_left_comp },
        unfold HasFinProduct.flatten.Proj,
        repeat { rw HomsOut.split_left_append },
        apply HomsOut.get.inj,
        apply funext, intro n, cases n with n ωn,
        rw HomsOut.get_comp,
        repeat { rw HomsOut.get_split_left },
        repeat { rw C^.circ_assoc },
        repeat { rw cast_hom.circ },
        rw -C^.circ_assoc,
        apply cast_hom.circ.congr_right,
        unfold HasFinProduct.flatten.univ,
        refine heq.trans _ (heq_of_eq (Cat.circ.congr_left (eq.symm (HomsOut.get_enum _ _)))),
        refine heq.trans _ (heq_of_eq (finproduct.univ.mediates C
                                        (factor₁ ++ [finproduct C factor₂] ++ factor₃)
                                        (HasFinProduct.flatten.univ.Proj factor₁ factor₂ factor₃ c hom)
                                        {val := n, is_lt := list.length.grow_left (list.length.grow_left ωn)})),
        unfold HasFinProduct.flatten.univ.Proj,
        refine heq.trans _ (heq.symm (HomsOut.get_append _ _ _ _)),
        refine heq.trans _ (heq.symm (HomsOut.get_append _ _ _ _)),
        repeat { rw HomsOut.get_split_left },
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


example (C : Cat) (x y z : ⟦C⟧)
        [xy_HasFinProduct : HasFinProduct C [x, y]]
        [xy_z_HasFinProduct : HasFinProduct C [finproduct C [x, y], z]]
        [yz_HasFinProduct : HasFinProduct C [y, z]]
        [x_yz_HasFinProduct : HasFinProduct C [x, finproduct C [y, z]]]
        : ⟦C : finproduct C [finproduct C [x, y], z] →→ finproduct C [x, finproduct C [y, z]]⟧
 := finproduct.iso (@HasFinProduct.flatten C [] [x, y] [z] xy_HasFinProduct xy_z_HasFinProduct)
                   (@HasFinProduct.flatten C [x] [y,z] [] yz_HasFinProduct x_yz_HasFinProduct)



/- -----------------------------------------------------------------------
Co-products.
----------------------------------------------------------------------- -/

/-! #brief A cone over a co-product.
-/
definition CoProductCone (C : Cat.{ℓobj ℓhom}) {A : Type ℓ}
    (factor : A → C^.obj)
    : Type (max ℓ ℓobj ℓhom)
:= ProductCone (OpCat C) factor

/-! #brief Helper for making a product cone.
-/
definition CoProductCone.mk {C : Cat.{ℓobj ℓhom}} {A : Type ℓ}
    {factor : A → C^.obj}
    (c : C^.obj)
    (incl : ∀ (a : A), C^.hom (factor a) c)
    : CoProductCone C factor
:= ProductCone.mk c incl

/-! #brief A co-product in a category.
-/
@[class] definition HasCoProduct (C : Cat.{ℓobj ℓhom}) {A : Type ℓ}
    (factor : A → C^.obj)
:= HasProduct (OpCat C) factor

instance HasCoProduct.HasProduct {C : Cat.{ℓobj ℓhom}} {A : Type ℓ}
    (factor : A → C^.obj)
    [factor_HasCoProduct : HasCoProduct C factor]
    : HasProduct (OpCat C) factor
:= factor_HasCoProduct

/-! #brief A category with all co-products.
-/
class HasAllCoProducts (C : Cat.{ℓobj ℓhom})
:= (has_coproduct : ∀ {A : Type ℓ} (factor : A → C^.obj)
                    , HasCoProduct C factor)

instance HasAllCoProducts.HasCoProduct (C : Cat.{ℓobj ℓhom})
    [C_HasAllCoProducts : HasAllCoProducts.{ℓ} C]
    {A : Type ℓ} (factor : A → C^.obj)
    : HasCoProduct C factor
:= HasAllCoProducts.has_coproduct factor

/-! #brief Helper for showing a category has a co-product.
-/
definition HasCoProduct.show (C : Cat.{ℓobj ℓhom}) {A : Type ℓ}
    (factor : A → C^.obj)
    (p : C^.obj)
    (incl : ∀ (a : A), C^.hom (factor a) p)
    (univ
      : ∀ (c : C^.obj) (hom : ∀ (a : A), C^.hom (factor a) c)
        , C^.hom p c)
    (ωuniv
      : ∀ (c : C^.obj) (hom : ∀ (a : A), C^.hom (factor a) c)
           (a : A)
        , hom a = C^.circ (univ c hom) (incl a))
    (ωuniq
      : ∀ (c : C^.obj) (hom : ∀ (a : A), C^.hom (factor a) c)
           (h : C^.hom p c) (ωh : ∀ {a : A}, hom a = C^.circ h (incl a))
        , h = univ c hom)
    : HasCoProduct C factor
:= HasProduct.show (OpCat C) factor p incl univ ωuniv ωuniq

/-! #brief Co-products are cones.
-/
definition coproduct.cone (C : Cat.{ℓobj ℓhom}) {A : Type ℓ}
    (factor : A → C^.obj)
    [factor_HasCoProduct : HasCoProduct C factor]
    : CoProductCone C factor
:= product.cone (OpCat C) factor

/-! #brief The co-product of a collection of objects.
-/
definition coproduct (C : Cat.{ℓobj ℓhom}) {A : Type ℓ}
    (factor : A → C^.obj)
    [factor_HasCoProduct : HasCoProduct C factor]
    : C^.obj
:= (coproduct.cone C factor)^.obj

/-! #brief Inclusion into a co-product.
-/
definition coproduct.ι (C : Cat.{ℓobj ℓhom}) {A : Type ℓ}
    (factor : A → C^.obj)
    [factor_HasCoProduct : HasCoProduct C factor]
    (a : A)
    : C^.hom (factor a) (coproduct C factor)
:= product.π (OpCat C) factor a

/-! #brief Every cone is mediated through the co-product.
-/
definition coproduct.univ (C : Cat.{ℓobj ℓhom}) {A : Type ℓ}
    (factor : A → C^.obj)
    [factor_HasCoProduct : HasCoProduct C factor]
    (c : CoProductCone C factor)
    : C^.hom (coproduct C factor) c^.obj
:= product.univ (OpCat C) factor c

/-! #brief Every cone is mediated through the co-product.
-/
definition coproduct.univ.mediates (C : Cat.{ℓobj ℓhom}) {A : Type ℓ}
    (factor : A → C^.obj)
    {factor_HasCoProduct : HasCoProduct C factor}
    (c : CoProductCone C factor)
    (a : A)
    : c^.hom a = C^.circ (coproduct.univ C factor c) (@coproduct.ι C A factor factor_HasCoProduct a)
:= product.univ.mediates (OpCat C) factor c a

/-! #brief The mediating map from the co-product to the cone unique.
-/
definition coproduct.univ.uniq (C : Cat.{ℓobj ℓhom}) {A : Type ℓ}
    (factor : A → C^.obj)
    {factor_HasCoProduct : HasCoProduct C factor}
    (c : CoProductCone C factor)
    (m : C^.hom (coproduct C factor) c^.obj)
    (ω : ∀ (a : A), c^.hom a = m ∘∘ (@coproduct.ι C A factor factor_HasCoProduct a))
    : m = coproduct.univ C factor c
:= product.univ.uniq (OpCat C) factor c m ω

/-! #brief The unique iso between two coproducts of the same factors.
-/
definition coproduct.iso {C : Cat.{ℓobj ℓhom}} {A : Type ℓ}
    {factor : A → C^.obj}
    (factor_HasCoProduct₁ factor_HasCoProduct₂ : HasCoProduct C factor)
    : C^.hom (@coproduct C A factor factor_HasCoProduct₁)
             (@coproduct C A factor factor_HasCoProduct₂)
:= product.iso factor_HasCoProduct₂ factor_HasCoProduct₁

/-! #brief Co-products are unique up-to unique isomorphism.
-/
definition coproduct.uniq {C : Cat.{ℓobj ℓhom}} {A : Type ℓ}
    {factor : A → C^.obj}
    (factor_HasCoProduct₁ factor_HasCoProduct₂ : HasCoProduct C factor)
    : Iso (coproduct.iso factor_HasCoProduct₁ factor_HasCoProduct₂)
          (coproduct.iso factor_HasCoProduct₂ factor_HasCoProduct₁)
:= { id₁ := (product.uniq factor_HasCoProduct₂ factor_HasCoProduct₁)^.id₂
   , id₂ := (product.uniq factor_HasCoProduct₂ factor_HasCoProduct₁)^.id₁
   }

/-! #brief Factor-projection out of a certain kind of coproduct.
-/
definition coproduct.factor_out {C : Cat.{ℓobj (ℓhom + 1)}}
    [C_HasFinal : HasFinal C]
    {A : C^.obj}
    (factor : C^.hom (final C) A → C^.obj)
    [factor_HasCoProduct : HasCoProduct C factor]
    : C^.hom (coproduct C factor) A
:= coproduct.univ C factor
    (CoProductCone.mk A (λ a, C^.circ a (final_hom (factor a))))



/- -----------------------------------------------------------------------
Co-products in functor categories.
----------------------------------------------------------------------- -/

/-! #brief Co-products in functor categories can be computed pointwise.
-/
instance FunCat.HasCoProduct {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    [D_HasAllCoProducts : HasAllCoProducts.{ℓ} D]
    {A : Type ℓ} (factor : A → Fun C D)
    : HasCoProduct (FunCat C D) factor
:= sorry
-- := @FunCat.HasCoLimit C D _ begin end (ProductDrgm (FunCat C D) factor)

/-! #brief Co-products in functor categories can be computed pointwise.
-/
instance FunCat.HasAllCoProducts {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    [D_HasAllCoProducts : HasAllCoProducts.{ℓ} D]
    : HasAllCoProducts.{ℓ} (FunCat C D)
:= { has_coproduct := λ A factor, FunCat.HasCoProduct factor
   }



/- -----------------------------------------------------------------------
Finite co-products.
----------------------------------------------------------------------- -/

/-! #brief A cone over a finite co-product.
-/
definition FinCoProductCone (C : Cat.{ℓobj ℓhom})
    (factor : list C^.obj)
    : Type (max ℓobj ℓhom)
:= CoProductCone C (list.get factor)

/-! #brief Every finite co-product cone comes with inclusions.
-/
definition FinCoProductCone.Proj {C : Cat.{ℓobj ℓhom}}
    {factor : list C^.obj}
    (c : FinCoProductCone C factor)
    : HomsIn factor c^.obj
:= dlist.enum (Cone.hom c)

/-! #brief Helper for making a finite co-product cone.
-/
definition FinCoProductCone.mk {C : Cat.{ℓobj ℓhom}}
    {factor : list C^.obj}
    (c : C^.obj)
    (incl : HomsIn factor c)
    : FinCoProductCone C factor
:= CoProductCone.mk c (HomsIn.get incl)

/-! #brief A finite co-product in a category.
-/
@[class] definition HasFinCoProduct (C : Cat.{ℓobj ℓhom})
    (factor : list C^.obj)
:= HasCoProduct C (list.get factor)

instance HasFinCoProduct.HasCoProduct (C : Cat.{ℓobj ℓhom})
    (factor : list C^.obj)
    [factor_HasCoProduct : HasFinCoProduct C factor]
    : HasCoProduct C (list.get factor)
:= factor_HasCoProduct

/-! #brief A category with all finite co-products.
-/
class HasAllFinCoProducts (C : Cat.{ℓobj ℓhom})
:= (has_coproduct : ∀ (factor : list C^.obj), HasFinCoProduct C factor)

instance HasAllFinCoProducts.HasFinCoProduct (C : Cat.{ℓobj ℓhom})
    [C_HasAllFinCoProducts : HasAllFinCoProducts C]
    (factor : list C^.obj)
    : HasFinCoProduct C factor
:= HasAllFinCoProducts.has_coproduct factor

/-! #brief Helper for showing a category has a finite co-product.
-/
definition HasFinCoProduct.show {C : Cat.{ℓobj ℓhom}}
    (factor : list C^.obj)
    (p : C^.obj)
    (incl : HomsIn factor p)
    (univ : ∀ (c : C^.obj) (hom : HomsIn factor c)
            , C^.hom p c)
    (ωuniv : ∀ (c : C^.obj) (hom : HomsIn factor c)
             , hom = HomsIn.comp (univ c hom) incl)
    (ωuniq : ∀ (c : C^.obj) (hom : HomsIn factor c) (h : C^.hom p c)
               (ωcomm : hom = HomsIn.comp h incl)
             , h = univ c hom)
    : HasFinCoProduct C factor
:= @HasFinProduct.show (OpCat C) factor p incl univ ωuniv ωuniq

/-! #brief Finite co-products are cones.
-/
definition fincoproduct.cone (C : Cat.{ℓobj ℓhom})
    (factor : list C^.obj)
    [factor_HasFinCoProduct : HasFinCoProduct C factor]
    : FinCoProductCone C factor
:= coproduct.cone C (list.get factor)

/-! #brief The co-product of a finite collection of objects.
-/
definition fincoproduct (C : Cat.{ℓobj ℓhom})
    (factor : list C^.obj)
    [factor_HasFinCoProduct : HasFinCoProduct C factor]
    : C^.obj
:= (fincoproduct.cone C factor)^.obj

/-! #brief An esoteric but useful equality helper.
-/
theorem fincoproduct.eq {C : Cat.{ℓobj ℓhom}}
    [C_HasAllFinCoProducts : HasAllFinCoProducts C]
    : ∀ (factor₁ factor₂ : list C^.obj)
        (ωfactor : factor₁ = factor₂)
      , @fincoproduct C factor₁ (HasAllFinCoProducts.HasFinCoProduct C factor₁)
          = @fincoproduct C factor₂ (HasAllFinCoProducts.HasFinCoProduct C factor₂)
| factor .(factor) (eq.refl .(factor)) := rfl

/-! #brief Inclusion into a finite co-product.
-/
definition fincoproduct.ι (C : Cat.{ℓobj ℓhom})
    (factor : list C^.obj)
    [factor_HasFinCoProduct : HasFinCoProduct C factor]
    (n : fin (list.length factor))
    : C^.hom (list.get factor n) (fincoproduct C factor)
:= coproduct.ι C (list.get factor) n

/-! #brief Every cone is mediated through the co-product.
-/
definition fincoproduct.univ (C : Cat.{ℓobj ℓhom})
    (factor : list C^.obj)
    [factor_HasFinCoProduct : HasFinCoProduct C factor]
    {c : C^.obj} (hom : HomsIn factor c)
    : C^.hom (fincoproduct C factor) c
:= coproduct.univ C (list.get factor) (FinCoProductCone.mk c hom)

/-! #brief Every cone is mediated through the co-product.
-/
definition fincoproduct.univ.mediates (C : Cat.{ℓobj ℓhom})
    (factor : list C^.obj)
    [factor_HasFinCoProduct : HasFinCoProduct C factor]
    {c : C^.obj} (hom : HomsIn factor c)
    (n : fin (list.length factor))
    : HomsIn.get hom n = C^.circ (fincoproduct.univ C factor hom) (fincoproduct.ι C factor n)
:= coproduct.univ.mediates C (list.get factor) (FinCoProductCone.mk c hom) n

/-! #brief The mediating map from the cone to the product is unique.
-/
definition fincoproduct.univ.uniq (C : Cat.{ℓobj ℓhom})
    (factor : list C^.obj)
    [factor_HasFinCoProduct : HasFinCoProduct C factor]
    {c : C^.obj} (hom : HomsIn factor c)
    (m : C^.hom (fincoproduct C factor) c)
    (ω : hom = HomsIn.comp m (fincoproduct.cone C factor)^.Proj)
    : m = fincoproduct.univ C factor hom
:= @finproduct.univ.uniq (OpCat C) factor factor_HasFinCoProduct c hom m ω

/-! #brief The unique iso between two co-products of the same factors.
-/
definition fincoproduct.iso {C : Cat.{ℓobj ℓhom}}
    {factor : list C^.obj}
    (factor_HasFinCoProduct₁ factor_HasFinCoProduct₂ : HasFinCoProduct C factor)
    : C^.hom (@fincoproduct C factor factor_HasFinCoProduct₁)
             (@fincoproduct C factor factor_HasFinCoProduct₂)
:= coproduct.iso factor_HasFinCoProduct₁ factor_HasFinCoProduct₂

/-! #brief Finite products are unique up-to unique isomorphism.
-/
definition fincoproduct.uniq {C : Cat.{ℓobj ℓhom}}
    {factor : list C^.obj}
    (factor_HasFinCoProduct₁ factor_HasFinCoProduct₂ : HasFinCoProduct C factor)
    : Iso (fincoproduct.iso factor_HasFinCoProduct₁ factor_HasFinCoProduct₂)
          (fincoproduct.iso factor_HasFinCoProduct₂ factor_HasFinCoProduct₁)
:= coproduct.uniq factor_HasFinCoProduct₁ factor_HasFinCoProduct₂



/- -----------------------------------------------------------------------
Finite co-products in functor categories.
----------------------------------------------------------------------- -/

/-! #brief Finite co-products in functor categories can be computed pointwise.
-/
instance FunCat.HasFinCoProduct {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    [D_HasAllFinCoProducts : HasAllFinCoProducts D]
    (factor : list (Fun C D))
    : HasFinCoProduct (FunCat C D) factor
:= sorry

/-! #brief Co-products in functor categories can be computed pointwise.
-/
instance FunCat.HasAllCoFinProducts {C : Cat.{ℓobj₁ ℓhom₁}} {D : Cat.{ℓobj₂ ℓhom₂}}
    [D_HasAllFinCoProducts : HasAllFinCoProducts D]
    : HasAllFinCoProducts (FunCat C D)
:= { has_coproduct := λ factor, FunCat.HasFinCoProduct factor
   }



/- -----------------------------------------------------------------------
Finite co-products of homs.
----------------------------------------------------------------------- -/

/-! #brief The product of a list of homs.
-/
definition fincoproduct.hom {C : Cat.{ℓobj ℓhom}}
    {ccs : list (prod C^.obj C^.obj)}
    (fns : HomsList C ccs)
    [ccs_domFinCoProduct : HasFinCoProduct C (list.map prod.fst ccs)]
    [ccs_codomFinCoProduct : HasFinCoProduct C (list.map prod.snd ccs)]
    : C^.hom (fincoproduct C (list.map prod.fst ccs))
             (fincoproduct C (list.map prod.snd ccs))
:= fincoproduct.univ _ _ (homs_comp_in (fincoproduct.cone C (list.map prod.snd ccs))^.Proj fns)

end qp
