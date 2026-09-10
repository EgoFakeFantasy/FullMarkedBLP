import FullMarkedBLP.RankApplication
import FullMarkedBLP.RankWordEmbedding

namespace FullMarkedBLP
open FirstOrder Language

def RankGraphComposes {lambda : Ordinal.{u}} (left right result : RankDomain lambda) : Prop :=
  ∀ x y z : RankDomain lambda, rankGraphApplies right x y → rankGraphApplies left y z →
    rankGraphApplies result x z

def rankGraphComposesFormula : membershipLanguage.Formula (Fin 3) :=
  .all (.all (.all ((rankGraphAppliesAt (.inl 1) (.inr 0) (.inr 1)).imp
    ((rankGraphAppliesAt (.inl 0) (.inr 1) (.inr 2)).imp
      (rankGraphAppliesAt (.inl 2) (.inr 0) (.inr 2))))))

theorem rankGraphComposesFormula_realize {lambda : Ordinal.{u}} (left right result : RankDomain lambda) :
    rankGraphComposesFormula.Realize ![left, right, result] ↔ RankGraphComposes left right result := by
  simp [rankGraphComposesFormula, RankGraphComposes, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, rankGraphAppliesAt_realize, Fin.snoc]

theorem rankElementary_graphComposes_iff {lambda : Ordinal.{u}} (j : RankElementaryEmbedding lambda)
    (left right result : RankDomain lambda) :
    RankGraphComposes (j left) (j right) (j result) ↔ RankGraphComposes left right result := by
  have statement := j.map_formula rankGraphComposesFormula ![left, right, result]
  have same : j ∘ ![left, right, result] = ![j left, j right, j result] := by
    funext i
    rcases i with ⟨i, hi⟩
    match i with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | n + 3 => omega
  rw [same, rankGraphComposesFormula_realize, rankGraphComposesFormula_realize] at statement
  exact statement

theorem rankRestrictionGraph_composes {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (left right : RankElementaryEmbedding lambda) (domain : RankDomain lambda) :
    RankGraphComposes (rankRestrictionGraph hl left (right domain)) (rankRestrictionGraph hl right domain)
      (rankRestrictionGraph hl (left.comp right) domain) := by
  intro x y z rightEdge leftEdge
  obtain ⟨member, rightEq⟩ := (rankRestrictionGraph_applies_iff hl right domain x y).mp rightEdge
  have leftEq := ((rankRestrictionGraph_applies_iff hl left (right domain) y z).mp leftEdge).2
  apply (rankRestrictionGraph_applies_iff hl (left.comp right) domain x z).mpr
  exact ⟨member, (congrArg left rightEq).trans leftEq⟩

/-- Application distributes over ordinary composition on all inputs. -/
theorem rankApply_comp_right {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (outer left right : RankElementaryEmbedding lambda) :
    rankApply hl outer (left.comp right) = (rankApply hl outer left).comp (rankApply hl outer right) := by
  apply FirstOrder.Language.ElementaryEmbedding.ext
  intro x
  obtain ⟨domain, member⟩ := rankElementary_image_cofinal hl outer x
  have rightEdge : rankGraphApplies (outer (rankRestrictionGraph hl right domain)) x (rankApply hl outer right x) :=
    rankApplication_on_domain hl outer right (rankElementary_image_cofinal hl outer) domain x member
  have function := (rankIsFunction_iff hl _ _ _).mp (rankRestrictionGraph_image_function hl outer right domain)
  have middleMember := (ZFSet.pair_mem_prod.mp (function.1 ((rankGraphApplies_iff hl _ _ _).mp rightEdge))).2
  have leftEdge : rankGraphApplies (outer (rankRestrictionGraph hl left (right domain)))
      (rankApply hl outer right x) (rankApply hl outer left (rankApply hl outer right x)) :=
    rankApplication_on_domain hl outer left (rankElementary_image_cofinal hl outer) (right domain)
      (rankApply hl outer right x) middleMember
  have composition := (rankElementary_graphComposes_iff outer _ _ _).mpr (rankRestrictionGraph_composes hl left right domain)
  have result := composition x _ _ rightEdge leftEdge
  exact rankApplicationRel_functional hl outer (left.comp right) (rankApply_spec hl outer (left.comp right) x)
    ⟨domain, result⟩

theorem rankApply_refl {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j : RankElementaryEmbedding lambda) :
    rankApply hl j (ElementaryEmbedding.refl membershipLanguage (RankDomain lambda)) =
      ElementaryEmbedding.refl membershipLanguage (RankDomain lambda) := by
  let identity := ElementaryEmbedding.refl membershipLanguage (RankDomain lambda)
  have idempotent := rankApply_comp_right hl j identity identity
  apply ElementaryEmbedding.ext
  intro x
  have point := congrArg (fun f : RankElementaryEmbedding lambda => f x) idempotent
  change rankApply hl j identity x = rankApply hl j identity (rankApply hl j identity x) at point
  exact ((rankApply hl j identity).injective point).symm

theorem rankApply_word {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j : RankElementaryEmbedding lambda) (embedding : Nat → RankElementaryEmbedding lambda) (word : List Nat) :
    rankApply hl j (rankWordEmbedding embedding word) = rankWordEmbedding (fun i => rankApply hl j (embedding i)) word := by
  induction word with
  | nil => exact rankApply_refl hl j
  | cons i tail ih =>
    change rankApply hl j ((embedding i).comp (rankWordEmbedding embedding tail)) =
      (rankApply hl j (embedding i)).comp (rankWordEmbedding (fun i => rankApply hl j (embedding i)) tail)
    rw [rankApply_comp_right, ih]

end FullMarkedBLP
