import FullMarkedBLP.RankTruthMatrix

namespace FullMarkedBLP

theorem rankTableHolds_nat {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (hw : Ordinal.omega0 < lambda) {k : Nat} (relation : (Fin k → Nat) → Prop)
    (tuple : Fin k → Nat) :
    rankTableHolds hl (rankNatRelation hw relation) (rankNat hl ∘ tuple) ↔ relation tuple := by
  change (rankTuple hl (rankNat hl ∘ tuple)).val ∈ zfNatRelation relation ↔ _
  rw [rankTuple_nat, zfNatRelation_mem]

theorem rankArityTable_iff {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (hw : Ordinal.omega0 < lambda) (code arity : RankDomain lambda) :
    rankTableHolds hl (rankSyntaxBooks hw 0) ![code, arity] ↔
      ∃ (n : Nat) (phi : RankPredicateFormula 0 n),
        code = rankNat hl (rankSyntaxCode ⟨n, phi⟩) ∧ arity = rankNat hl n := by
  change (rankTuple hl ![code, arity]).val ∈ (rankNatRelation hw rankSyntaxArity).val ↔ _
  rw [rankTuple_mem_natRelation hl hw]
  constructor
  · rintro ⟨tuple, ⟨⟨n, phi⟩, hc, ha⟩, coords⟩
    refine ⟨n, phi, ?_, ?_⟩
    · simpa [Function.comp_def, hc] using congrFun coords 0
    · simpa [Function.comp_def, ha] using congrFun coords 1
  · rintro ⟨n, phi, rfl, rfl⟩
    exact ⟨![rankSyntaxCode ⟨n, phi⟩, n], ⟨⟨n, phi⟩, rfl, rfl⟩, (rankMapPair _ _ _).symm⟩

theorem rankFalseTable_iff {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (hw : Ordinal.omega0 < lambda) (code : RankDomain lambda) :
    rankTableHolds hl (rankSyntaxBooks hw 1) ![code] ↔
      ∃ n, code = rankNat hl (rankSyntaxCode ⟨n, .falsum⟩) := by
  change (rankTuple hl ![code]).val ∈ (rankNatRelation hw rankSyntaxFalse).val ↔ _
  rw [rankTuple_mem_natRelation hl hw]
  constructor
  · rintro ⟨tuple, ⟨n, hc⟩, coords⟩
    exact ⟨n, by simpa [Function.comp_def, hc] using congrFun coords 0⟩
  · rintro ⟨n, rfl⟩
    exact ⟨![rankSyntaxCode ⟨n, .falsum⟩], ⟨n, rfl⟩, (rankMapSingle _ _).symm⟩

theorem rankEqualTable_iff {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (hw : Ordinal.omega0 < lambda) (code i j : RankDomain lambda) :
    rankTableHolds hl (rankSyntaxBooks hw 2) ![code, i, j] ↔
      ∃ (n : Nat) (x y : Fin n), code = rankNat hl (rankSyntaxCode ⟨n, .equal x y⟩) ∧
        i = rankNat hl x.val ∧ j = rankNat hl y.val := by
  change (rankTuple hl ![code, i, j]).val ∈ (rankNatRelation hw rankSyntaxEqual).val ↔ _
  rw [rankTuple_mem_natRelation hl hw]
  constructor
  · rintro ⟨tuple, ⟨n, x, y, hc, hi, hj⟩, coords⟩
    refine ⟨n, x, y, ?_, ?_, ?_⟩
    · simpa [Function.comp_def, hc] using congrFun coords 0
    · simpa [Function.comp_def, hi] using congrFun coords 1
    · simpa [Function.comp_def, hj] using congrFun coords 2
  · rintro ⟨n, x, y, rfl, rfl, rfl⟩
    exact ⟨![rankSyntaxCode ⟨n, .equal x y⟩, x.val, y.val],
      ⟨n, x, y, rfl, rfl, rfl⟩, (rankMapTriple _ _ _ _).symm⟩

theorem rankMemberTable_iff {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (hw : Ordinal.omega0 < lambda) (code i j : RankDomain lambda) :
    rankTableHolds hl (rankSyntaxBooks hw 3) ![code, i, j] ↔
      ∃ (n : Nat) (x y : Fin n), code = rankNat hl (rankSyntaxCode ⟨n, .member x y⟩) ∧
        i = rankNat hl x.val ∧ j = rankNat hl y.val := by
  change (rankTuple hl ![code, i, j]).val ∈ (rankNatRelation hw rankSyntaxMember).val ↔ _
  rw [rankTuple_mem_natRelation hl hw]
  constructor
  · rintro ⟨tuple, ⟨n, x, y, hc, hi, hj⟩, coords⟩
    refine ⟨n, x, y, ?_, ?_, ?_⟩
    · simpa [Function.comp_def, hc] using congrFun coords 0
    · simpa [Function.comp_def, hi] using congrFun coords 1
    · simpa [Function.comp_def, hj] using congrFun coords 2
  · rintro ⟨n, x, y, rfl, rfl, rfl⟩
    exact ⟨![rankSyntaxCode ⟨n, .member x y⟩, x.val, y.val],
      ⟨n, x, y, rfl, rfl, rfl⟩, (rankMapTriple _ _ _ _).symm⟩

theorem rankImpTable_iff {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (hw : Ordinal.omega0 < lambda) (code left right : RankDomain lambda) :
    rankTableHolds hl (rankSyntaxBooks hw 4) ![code, left, right] ↔
      ∃ (n : Nat) (p q : RankPredicateFormula 0 n),
        code = rankNat hl (rankSyntaxCode ⟨n, .imp p q⟩) ∧
        left = rankNat hl (rankSyntaxCode ⟨n, p⟩) ∧ right = rankNat hl (rankSyntaxCode ⟨n, q⟩) := by
  change (rankTuple hl ![code, left, right]).val ∈ (rankNatRelation hw rankSyntaxImp).val ↔ _
  rw [rankTuple_mem_natRelation hl hw]
  constructor
  · rintro ⟨tuple, ⟨n, p, q, hc, hp, hq⟩, coords⟩
    refine ⟨n, p, q, ?_, ?_, ?_⟩
    · simpa [Function.comp_def, hc] using congrFun coords 0
    · simpa [Function.comp_def, hp] using congrFun coords 1
    · simpa [Function.comp_def, hq] using congrFun coords 2
  · rintro ⟨n, p, q, rfl, rfl, rfl⟩
    exact ⟨![rankSyntaxCode ⟨n, .imp p q⟩, rankSyntaxCode ⟨n, p⟩, rankSyntaxCode ⟨n, q⟩],
      ⟨n, p, q, rfl, rfl, rfl⟩, (rankMapTriple _ _ _ _).symm⟩

theorem rankAllTable_iff {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (hw : Ordinal.omega0 < lambda) (code body : RankDomain lambda) :
    rankTableHolds hl (rankSyntaxBooks hw 5) ![code, body] ↔
      ∃ (n : Nat) (p : RankPredicateFormula 0 (n + 1)),
        code = rankNat hl (rankSyntaxCode ⟨n, .all p⟩) ∧ body = rankNat hl (rankSyntaxCode ⟨n + 1, p⟩) := by
  change (rankTuple hl ![code, body]).val ∈ (rankNatRelation hw rankSyntaxAll).val ↔ _
  rw [rankTuple_mem_natRelation hl hw]
  constructor
  · rintro ⟨tuple, ⟨n, p, hc, hp⟩, coords⟩
    refine ⟨n, p, ?_, ?_⟩
    · simpa [Function.comp_def, hc] using congrFun coords 0
    · simpa [Function.comp_def, hp] using congrFun coords 1
  · rintro ⟨n, p, rfl, rfl⟩
    exact ⟨![rankSyntaxCode ⟨n, .all p⟩, rankSyntaxCode ⟨n + 1, p⟩],
      ⟨n, p, rfl, rfl⟩, (rankMapPair _ _ _).symm⟩

theorem rankNat_injective {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda) :
    Function.Injective (rankNat hl) := by
  intro n m same
  exact Nat.cast_injective (Ordinal.toZFSet_injective (congrArg Subtype.val same))

theorem rankAssignmentAtCode_iff {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (hw : Ordinal.omega0 < lambda) (code assignment : RankDomain lambda) :
    rankAssignmentAtCode hl (rankSyntaxBooks hw 0) code assignment ↔
      rankValidAssignment hl code assignment := by
  let values := ![rankSyntaxBooks hw 0, code, assignment]
  exact (rankFormulaValidAssignment_realize_raw hl (0 : Fin 3) 1 2
    (fun _ : Fin 0 => Set.univ) values).symm.trans
      (rankFormulaValidAssignment_realize hl hw 0 1 2 (fun _ : Fin 0 => Set.univ) values rfl)

theorem rankValidAssignment_formula_iff {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {n : Nat} (phi : RankPredicateFormula 0 n) (assignment : RankDomain lambda) :
    rankValidAssignment hl (rankNat hl (rankSyntaxCode ⟨n, phi⟩)) assignment ↔
      ∃ values : Fin n → RankDomain lambda, assignment = rankAssignment hl values := by
  constructor
  · rintro ⟨k, psi, values, same, hass⟩
    have formulas := rankSyntaxCode_injective (rankNat_injective hl same)
    have arity : n = k := (Sigma.mk.inj formulas).1
    subst k
    exact ⟨values, hass⟩
  · rintro ⟨values, rfl⟩
    exact ⟨n, phi, values, rfl, rfl⟩

theorem rankAssignment_applies_nat_iff {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {n : Nat} (values : Fin n → RankDomain lambda) (i : Fin n) (output : RankDomain lambda) :
    rankGraphApplies (rankAssignment hl values) (rankNat hl i.val) output ↔ values i = output := by
  rw [rankAssignment_applies_iff hl]
  constructor
  · rintro ⟨k, same, hout⟩
    have hik : i = k := Fin.ext (Nat.cast_injective (Ordinal.toZFSet_injective same))
    exact hik ▸ hout
  · exact fun h => ⟨i, rfl, h⟩

end FullMarkedBLP
