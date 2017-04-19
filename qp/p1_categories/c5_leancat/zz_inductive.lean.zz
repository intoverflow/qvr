/- -----------------------------------------------------------------------
Inductive types.
----------------------------------------------------------------------- -/

import .s1_basic
import .s2_depprod

namespace qp

open stdaux

universe variables ℓ



/- -----------------------------------------------------------------------
Inductive types.
----------------------------------------------------------------------- -/

-- /-! #brief Algebra structure on the decomposition of an inductive type.
-- -/
-- definition LeanCat.indType.alg
--     (σ : IndSig LeanCat.{ℓ})
--     [σ_HasIndType : @HasIndType LeanCat
--                        LeanCat.HasFinal
--                        LeanCat.HasDepProd
--                        LeanCat.HasAllPullbacks
--                        LeanCat.HasAllFinProducts
--                        LeanCat.HasAllFinCoProducts
--                        σ]
--     : EndoAlg (LeanCat.PolyEndoFun σ^.induce)
-- := { carr := @indType.decomp LeanCat
--                 LeanCat.HasFinal
--                 LeanCat.HasDepProd
--                 LeanCat.HasAllPullbacks
--                 LeanCat.HasAllFinProducts
--                 LeanCat.HasAllFinCoProducts
--                 σ σ_HasIndType
--    , hom := λ x, @ListSum.map (ConSig LeanCat) ConSig.codom
--                     (@indType.arg LeanCat
--                       LeanCat.HasFinal
--                       LeanCat.HasDepProd
--                       LeanCat.HasAllPullbacks
--                       LeanCat.HasAllFinProducts
--                       LeanCat.HasAllFinCoProducts
--                       σ σ_HasIndType)
--                     σ
--                     (λ n ωn args, (args, let foo := λ (m : ℕ) (ωm : m < (list.get σ {val := n, is_lt := ωn})^.fst)
--                                                     , (x^.snd { val := ListSum.ι _ { val := n, is_lt := cast begin rw list.length_map end ωn }
--                                                                        (cast (list.get_map (eq.symm (list.length_map ConSig.dom σ)))
--                                                                          (ListSum.ι _ { val := m, is_lt := cast begin rw list.length_repeat end ωm }
--                                                                            (cast list.get_repeat args)))
--                                                              , property := sorry
--                                                              })^.val
--                                       in begin dsimp end))
--                     x^.fst
--    }

end qp
