import FullMarkedBLP.RankTupleFormula

namespace FullMarkedBLP

/-- Exact extension of a set graph by the indicated single ordered pair. -/
def rankFormulaAppend {m n : Nat} (old new index value : Fin n) : RankPredicateFormula m n :=
  .all ((RankPredicateFormula.member (Fin.last n) new.castSucc).iff
    ((RankPredicateFormula.member (Fin.last n) old.castSucc).or
      (rankFormulaOrderedPair (Fin.last n) index.castSucc value.castSucc)))

theorem rankFormulaAppend_realize {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {m n : Nat} (old new index value : Fin n) (classes : Fin m → RankClass lambda)
    (values : Fin n → RankDomain lambda) :
    (rankFormulaAppend old new index value).Realize classes values ↔
      (values new).val = (values old).val ∪ {ZFSet.pair (values index).val (values value).val} := by
  simp only [rankFormulaAppend, RankPredicateFormula.Realize, RankPredicateFormula.realize_iff,
    RankPredicateFormula.realize_or, rankFormulaOrderedPair_realize,
    Fin.snoc_last, Fin.snoc_castSucc]
  constructor
  · intro h
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_union, ZFSet.mem_singleton]
    constructor
    · intro hz
      have result := (h (rankMember (values new) z hz)).mp hz
      exact result.imp_right ((rankIsOrderedPair_iff hl _ _ _).mp)
    · intro hz
      rcases hz with hz | rfl
      · exact (h (rankMember (values old) z hz)).mpr (Or.inl hz)
      · exact (h (rankOrderedPair hl (values index) (values value))).mpr
          (Or.inr ((rankIsOrderedPair_iff hl _ _ _).mpr rfl))
  · intro same z
    rw [same, ZFSet.mem_union, ZFSet.mem_singleton, rankIsOrderedPair_iff hl]

theorem rankAssignment_append_iff {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {n : Nat} (values : Fin n → RankDomain lambda) (x graph : RankDomain lambda) :
    graph.val = (rankAssignment hl values).val ∪ {ZFSet.pair (rankNat hl n).val x.val} ↔
      graph = rankAssignment hl (Fin.snoc values x) := by
  change graph.val = (rankAssignment hl values).val ∪ {ZFSet.pair (n : Ordinal).toZFSet x.val} ↔ _
  rw [← rankAssignment_snoc hl]
  exact ⟨Subtype.ext, congrArg Subtype.val⟩

def rankFormulaValidAssignment {m n : Nat} (arityBook code assignment : Fin n) : RankPredicateFormula m n :=
  ((rankFormulaTupleMem arityBook.castSucc ![code.castSucc, Fin.last n]).and
    (rankFormulaAssignment assignment.castSucc (Fin.last n))).ex

def rankValidAssignment {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (code assignment : RankDomain lambda) : Prop :=
  ∃ (n : Nat) (phi : RankPredicateFormula 0 n) (values : Fin n → RankDomain lambda),
    code = rankNat hl (rankSyntaxCode ⟨n, phi⟩) ∧ assignment = rankAssignment hl values

theorem rankFormulaValidAssignment_realize {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (hw : Ordinal.omega0 < lambda) {m n : Nat} (arityBook code assignment : Fin n)
    (classes : Fin m → RankClass lambda) (values : Fin n → RankDomain lambda)
    (book : values arityBook = rankNatRelation hw rankSyntaxArity) :
    (rankFormulaValidAssignment arityBook code assignment).Realize classes values ↔
      rankValidAssignment hl (values code) (values assignment) := by
  simp only [rankFormulaValidAssignment, RankPredicateFormula.realize_ex,
    RankPredicateFormula.realize_and, rankFormulaTupleMem_realize hl,
    rankFormulaAssignment_realize, Fin.snoc_castSucc, Fin.snoc_last]
  constructor
  · rintro ⟨arity, coded, range, function⟩
    rw [book] at coded
    obtain ⟨tuple, ⟨⟨k, phi⟩, hcode, harity⟩, coords⟩ :=
      (rankTuple_mem_natRelation hl hw _ _).mp coded
    have hc : values code = rankNat hl (rankSyntaxCode ⟨k, phi⟩) := by
      simpa [Function.comp_def, hcode] using congrFun coords 0
    have ha : arity = rankNat hl k := by
      simpa [Function.comp_def, harity] using congrFun coords 1
    rw [ha] at function
    obtain ⟨assignmentValues, same⟩ := rankAssignment_decode hl k function
    exact ⟨k, phi, assignmentValues, hc, same.symm⟩
  · rintro ⟨k, phi, assignmentValues, hcode, hass⟩
    refine ⟨rankNat hl k, ?_, rankFiniteRange hl assignmentValues, ?_⟩
    · rw [book]
      apply (rankTuple_mem_natRelation hl hw _ _).mpr
      refine ⟨![rankSyntaxCode ⟨k, phi⟩, k], ⟨⟨k, phi⟩, rfl, rfl⟩, ?_⟩
      funext i
      have cases : i = 0 ∨ i = 1 := by
        rcases i with ⟨i, hi⟩
        rcases (show i = 0 ∨ i = 1 by omega) with h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Fin.ext h)
      rcases cases with rfl | rfl <;> simp [hcode]
    · rw [hass]
      exact rankAssignment_isFunction hl assignmentValues

end FullMarkedBLP
