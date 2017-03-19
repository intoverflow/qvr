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

/-! #brief Helper for showing a category has a finite product.
-/
definition HasFinProduct.show {C : Cat.{ℓobj ℓhom}}
    {factor : list C^.obj}
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
:= HasProduct.show C p (HomsOut.get proj)
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
    : HomsOut (finproduct C (factor₁ ++ [finproduct C factor₂] ++ factor₃))
                     (factor₁ ++ factor₂ ++ factor₃)
:= let prj₁₂₃ : HomsOut (finproduct C (factor₁ ++ [finproduct C factor₂] ++ factor₃))
                              (factor₁ ++ [finproduct C factor₂] ++ factor₃)
           := (@finproduct.cone _ _ factor₁₂₃_HasFinProduct)^.Proj in
   let f₁ : HomsOut (finproduct C (factor₁ ++ [finproduct C factor₂] ++ factor₃)) factor₁
         := HomsOut.split_left (HomsOut.split_left prj₁₂₃) in
   let f₂ : HomsOut (finproduct C (factor₁ ++ [finproduct C factor₂] ++ factor₃)) [finproduct C factor₂]
         := HomsOut.split_right (HomsOut.split_left prj₁₂₃) in
   let f₂' := HomsOut.comp (@finproduct.cone _ _ factor₂_HasFinProduct)^.Proj (dlist.head f₂) in
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
:= HasFinProduct.show
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

end qp
