import FullMarkedBLP.RankSyntaxTableDecoding

namespace FullMarkedBLP

theorem rankAssignmentAtCode_formula {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (hw : Ordinal.omega0 < lambda) {n : Nat} (phi : RankPredicateFormula 0 n)
    (values : Fin n → RankDomain lambda) :
    rankAssignmentAtCode hl (rankSyntaxBooks hw 0)
      (rankNat hl (rankSyntaxCode ⟨n, phi⟩)) (rankAssignment hl values) :=
  (rankAssignmentAtCode_iff hl hw _ _).mpr ⟨n, phi, values, rfl, rfl⟩

theorem RankCodedTruthConditions.conditions {lambda : Ordinal.{u}} {hl : Order.IsSuccLimit lambda}
    {hw : Ordinal.omega0 < lambda} {truth : RankClass lambda}
    (conditions : RankCodedTruthConditions hl (rankSyntaxBooks hw) truth) :
    RankTruthConditions hl truth := by
  constructor
  · intro n values
    exact conditions.falsum _ _ (rankAssignmentAtCode_formula hl hw .falsum values)
      ((rankFalseTable_iff hl hw _).mpr ⟨n, rfl⟩)
  · intro n i j values
    exact conditions.equal _ _ _ _ _ _ (rankAssignmentAtCode_formula hl hw (.equal i j) values)
      ((rankEqualTable_iff hl hw _ _ _).mpr ⟨n, i, j, rfl, rfl, rfl⟩)
      (rankAssignment_get hl values i) (rankAssignment_get hl values j)
  · intro n i j values
    exact conditions.member _ _ _ _ _ _ (rankAssignmentAtCode_formula hl hw (.member i j) values)
      ((rankMemberTable_iff hl hw _ _ _).mpr ⟨n, i, j, rfl, rfl, rfl⟩)
      (rankAssignment_get hl values i) (rankAssignment_get hl values j)
  · intro n p q values
    exact conditions.imp _ _ _ _ (rankAssignmentAtCode_formula hl hw (.imp p q) values)
      ((rankImpTable_iff hl hw _ _ _).mpr ⟨n, p, q, rfl, rfl, rfl⟩)
  · intro n p values
    have result := conditions.all _ _ _ _
      ((rankArityTable_iff hl hw _ _).mpr ⟨n, .all p, rfl, rfl⟩)
      ⟨rankFiniteRange hl values, rankAssignment_isFunction hl values⟩
      ((rankAllTable_iff hl hw _ _).mpr ⟨n, p, rfl, rfl⟩)
    refine result.trans ?_
    constructor
    · intro h x
      exact h x (rankAssignment hl (Fin.snoc values x))
        ((rankAssignment_append_iff hl values x _).mpr rfl)
    · intro h x new same
      rw [(rankAssignment_append_iff hl values x new).mp same]
      exact h x

theorem RankTruthConditions.coded {lambda : Ordinal.{u}} {hl : Order.IsSuccLimit lambda}
    (hw : Ordinal.omega0 < lambda) {truth : RankClass lambda}
    (conditions : RankTruthConditions hl truth) :
    RankCodedTruthConditions hl (rankSyntaxBooks hw) truth := by
  constructor
  · intro code assignment valid coded
    obtain ⟨n, rfl⟩ := (rankFalseTable_iff hl hw _).mp coded
    obtain ⟨values, rfl⟩ := (rankValidAssignment_formula_iff hl _ _).mp
      ((rankAssignmentAtCode_iff hl hw _ _).mp valid)
    exact conditions.falsum n values
  · intro code assignment i j x y valid coded hx hy
    obtain ⟨n, a, b, rfl, rfl, rfl⟩ := (rankEqualTable_iff hl hw _ _ _).mp coded
    obtain ⟨values, rfl⟩ := (rankValidAssignment_formula_iff hl _ _).mp
      ((rankAssignmentAtCode_iff hl hw _ _).mp valid)
    have hax := (rankAssignment_applies_nat_iff hl values a x).mp hx
    have hby := (rankAssignment_applies_nat_iff hl values b y).mp hy
    rw [← hax, ← hby]
    exact conditions.equal n a b values
  · intro code assignment i j x y valid coded hx hy
    obtain ⟨n, a, b, rfl, rfl, rfl⟩ := (rankMemberTable_iff hl hw _ _ _).mp coded
    obtain ⟨values, rfl⟩ := (rankValidAssignment_formula_iff hl _ _).mp
      ((rankAssignmentAtCode_iff hl hw _ _).mp valid)
    have hax := (rankAssignment_applies_nat_iff hl values a x).mp hx
    have hby := (rankAssignment_applies_nat_iff hl values b y).mp hy
    rw [← hax, ← hby]
    exact conditions.member n a b values
  · intro code assignment left right valid coded
    obtain ⟨n, p, q, rfl, rfl, rfl⟩ := (rankImpTable_iff hl hw _ _ _).mp coded
    obtain ⟨values, rfl⟩ := (rankValidAssignment_formula_iff hl _ _).mp
      ((rankAssignmentAtCode_iff hl hw _ _).mp valid)
    exact conditions.imp n p q values
  · intro code assignment body arity arityCoded function allCoded
    obtain ⟨n, p, rfl, rfl⟩ := (rankAllTable_iff hl hw _ _).mp allCoded
    obtain ⟨m, psi, same, arityEq⟩ := (rankArityTable_iff hl hw _ _).mp arityCoded
    have formulas := rankSyntaxCode_injective (rankNat_injective hl same)
    have arities : n = m := (Sigma.mk.inj formulas).1
    subst m
    obtain ⟨range, function⟩ := function
    rw [arityEq] at function ⊢
    obtain ⟨values, rfl⟩ := rankAssignment_decode hl n function
    refine (conditions.all n p values).trans ?_
    constructor
    · intro h x new same
      rw [(rankAssignment_append_iff hl values x new).mp same]
      exact h x
    · intro h x
      exact h x (rankAssignment hl (Fin.snoc values x))
        ((rankAssignment_append_iff hl values x _).mpr rfl)

/-- The actual finite matrix, with actual fixed-rank tables, is equivalent
to the entire semantic truth recursion. This is not an infinitary schema
being declared to count as a formula. -/
theorem rankTruthMatrix_correct {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (hw : Ordinal.omega0 < lambda) (truth : RankClass lambda) :
    rankTruthMatrix.Realize (fun _ => truth) (rankSyntaxBooks hw) ↔ RankTruthConditions hl truth :=
  (rankTruthMatrix_realize hl _ truth).trans ⟨RankCodedTruthConditions.conditions, RankTruthConditions.coded hw⟩

theorem rankSatisfaction_matrix {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (hw : Ordinal.omega0 < lambda) :
    rankTruthMatrix.Realize (fun _ => rankSatisfaction hl) (rankSyntaxBooks hw) :=
  (rankTruthMatrix_correct hl hw _).mpr (rankSatisfaction_conditions hl)

theorem rankTruthMatrix_truth {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (hw : Ordinal.omega0 < lambda) {truth : RankClass lambda}
    (matrix : rankTruthMatrix.Realize (fun _ => truth) (rankSyntaxBooks hw))
    {n : Nat} (phi : RankPredicateFormula 0 n) (values : Fin n → RankDomain lambda) :
    rankFormulaTruth hl truth phi values ↔ phi.Realize Fin.elim0 values :=
  ((rankTruthMatrix_correct hl hw truth).mp matrix).realize phi values

theorem rankSyntaxBooks_rank_le {lambda : Ordinal.{u}} (hw : Ordinal.omega0 < lambda)
    (i : Fin 6) : (rankSyntaxBooks hw i).val.rank ≤ Ordinal.omega0 := by
  rcases i with ⟨i, hi⟩
  match i with
  | 0 => exact zfNatRelation_rank_le _
  | 1 => exact zfNatRelation_rank_le _
  | 2 => exact zfNatRelation_rank_le _
  | 3 => exact zfNatRelation_rank_le _
  | 4 => exact zfNatRelation_rank_le _
  | 5 => exact zfNatRelation_rank_le _
  | i + 6 => omega

end FullMarkedBLP
