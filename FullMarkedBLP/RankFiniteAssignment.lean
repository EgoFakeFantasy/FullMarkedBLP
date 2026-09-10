import FullMarkedBLP.RankGraphOrder

namespace FullMarkedBLP

noncomputable def rankNat {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda) (n : Nat) : RankDomain lambda :=
  ordinalDomainElement ⟨n, Ordinal.natCast_lt_of_isSuccLimit hl n⟩

noncomputable def finZFSetEquiv (n : Nat) : Fin n ≃ (n : Ordinal.{u}).toZFSet :=
  Equiv.ofBijective (fun i => ⟨(i.val : Ordinal).toZFSet,
    Ordinal.toZFSet_mem_toZFSet_iff.mpr (Nat.cast_lt.mpr i.isLt)⟩) (by
      constructor
      · intro i j same
        exact Fin.ext (Nat.cast_injective (Ordinal.toZFSet_injective (congrArg Subtype.val same)))
      · intro x
        obtain ⟨o, below, same⟩ := Ordinal.mem_toZFSet_iff.mp x.property
        obtain ⟨m, hm⟩ := Ordinal.lt_omega0.mp (below.trans (Ordinal.natCast_lt_omega0 n))
        rw [hm] at below same
        exact ⟨⟨m, Nat.cast_lt.mp below⟩, Subtype.ext same⟩)

theorem rankFiniteRange_bound {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {n : Nat} (values : Fin n → RankDomain lambda) :
    (ZFSet.range (fun i => (values i).val)).rank < lambda := by
  let bound : Ordinal.{u} := Finset.univ.sup (fun i => (values i).val.rank)
  have small : bound < lambda := (Finset.sup_lt_iff hl.pos).mpr (fun i _ => (values i).property)
  have included : ZFSet.range (fun i => (values i).val) ⊆ ZFSet.vonNeumann (Order.succ bound) := by
    intro x hx
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.mp hx
    exact ZFSet.mem_vonNeumann.mpr ((Finset.le_sup (Finset.mem_univ i)).trans_lt (Order.lt_succ bound))
  exact (ZFSet.rank_mono included).trans_lt (by
    simpa only [ZFSet.rank_vonNeumann] using hl.succ_lt small)

noncomputable def rankFiniteRange {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {n : Nat} (values : Fin n → RankDomain lambda) : RankDomain lambda :=
  ⟨ZFSet.range (fun i => (values i).val), rankFiniteRange_bound hl values⟩

noncomputable def rankAssignmentFunction {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {n : Nat} (values : Fin n → RankDomain lambda) :
    (rankNat hl n).val → (rankFiniteRange hl values).val :=
  fun i => ⟨(values ((finZFSetEquiv n).symm i)).val, ZFSet.mem_range.mpr ⟨_, rfl⟩⟩

/-- A finite assignment is an actual set function with domain the finite
von Neumann ordinal. Its values may be any sets in the ambient rank domain. -/
noncomputable def rankAssignment {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {n : Nat} (values : Fin n → RankDomain lambda) : RankDomain lambda :=
  rankFunctionGraph hl (rankNat hl n) (rankFiniteRange hl values) (rankAssignmentFunction hl values)

theorem rankAssignment_isFunction {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {n : Nat} (values : Fin n → RankDomain lambda) :
    rankIsFunction (rankAssignment hl values) (rankNat hl n) (rankFiniteRange hl values) :=
  rankFunctionGraph_isFunction hl _ _ _

theorem rankAssignment_applies_iff {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {n : Nat} (values : Fin n → RankDomain lambda) (input output : RankDomain lambda) :
    rankGraphApplies (rankAssignment hl values) input output ↔
      ∃ i : Fin n, input.val = (i.val : Ordinal).toZFSet ∧ values i = output := by
  rw [rankAssignment, rankFunctionGraph_applies_iff hl]
  constructor
  · rintro ⟨member, same⟩
    let i := (finZFSetEquiv n).symm ⟨input.val, member⟩
    refine ⟨i, ?_, Subtype.ext same⟩
    exact (congrArg (fun x : (n : Ordinal).toZFSet => x.val)
      ((finZFSetEquiv n).apply_symm_apply ⟨input.val, member⟩)).symm
  · rintro ⟨i, inputEq, outputEq⟩
    have member : input.val ∈ (rankNat hl n).val := by
      rw [inputEq]
      exact Ordinal.toZFSet_mem_toZFSet_iff.mpr (Nat.cast_lt.mpr i.isLt)
    refine ⟨member, ?_⟩
    have same : (⟨input.val, member⟩ : (n : Ordinal).toZFSet) = finZFSetEquiv n i := Subtype.ext inputEq
    change (values ((finZFSetEquiv n).symm ⟨input.val, member⟩)).val = output.val
    rw [same, Equiv.symm_apply_apply, outputEq]

theorem rankAssignment_get {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {n : Nat} (values : Fin n → RankDomain lambda) (i : Fin n) :
    rankGraphApplies (rankAssignment hl values) (rankNat hl i.val) (values i) :=
  (rankAssignment_applies_iff hl values _ _).mpr ⟨i, rfl, rfl⟩

theorem rankAssignment_mem_iff {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {n : Nat} (values : Fin n → RankDomain lambda) (p : ZFSet.{u}) :
    p ∈ (rankAssignment hl values).val ↔
      ∃ i : Fin n, p = ZFSet.pair (i.val : Ordinal).toZFSet (values i).val := by
  constructor
  · intro member
    let p' := rankMember (rankAssignment hl values) p member
    obtain ⟨x, y, _, _, pair⟩ := (rankAssignment_isFunction hl values).1 p' member
    obtain ⟨i, inputEq, outputEq⟩ := (rankAssignment_applies_iff hl values x y).mp ⟨p', member, pair⟩
    refine ⟨i, ?_⟩
    have same := (rankIsOrderedPair_iff hl p' x y).mp pair
    rwa [inputEq, ← outputEq] at same
  · rintro ⟨i, rfl⟩
    exact (rankGraphApplies_iff hl _ _ _).mp (rankAssignment_get hl values i)

/-- Appending the quantified value is an exact finite graph update. -/
theorem rankAssignment_snoc {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {n : Nat} (values : Fin n → RankDomain lambda) (x : RankDomain lambda) :
    (rankAssignment hl (Fin.snoc values x)).val =
      (rankAssignment hl values).val ∪ {ZFSet.pair (n : Ordinal).toZFSet x.val} := by
  apply ZFSet.ext
  intro p
  rw [rankAssignment_mem_iff, ZFSet.mem_union, ZFSet.mem_singleton, rankAssignment_mem_iff]
  constructor
  · rintro ⟨i, same⟩
    cases i using Fin.lastCases with
    | last => exact Or.inr (by simpa [Fin.snoc] using same)
    | cast i => exact Or.inl ⟨i, by simpa [Fin.snoc] using same⟩
  · rintro (⟨i, same⟩ | same)
    · exact ⟨i.castSucc, by simpa [Fin.snoc] using same⟩
    · exact ⟨Fin.last n, by simpa [Fin.snoc] using same⟩

theorem rankAssignment_injective {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda) {n : Nat} :
    Function.Injective (@rankAssignment lambda hl n) := by
  intro values other same
  funext i
  have edge := rankAssignment_get hl values i
  rw [same] at edge
  obtain ⟨k, indexEq, valueEq⟩ := (rankAssignment_applies_iff hl other _ _).mp edge
  have sameIndex : i = k := Fin.ext (Nat.cast_injective (Ordinal.toZFSet_injective indexEq))
  subst k
  exact valueEq.symm

/-- Every set function on the finite ordinal decodes to one of these
assignments, even if its supplied range bound contains unused values. -/
theorem rankAssignment_decode {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (n : Nat) {graph range : RankDomain lambda}
    (function : rankIsFunction graph (rankNat hl n) range) :
    ∃ values : Fin n → RankDomain lambda, rankAssignment hl values = graph := by
  have hf := (rankIsFunction_iff hl _ _ _).mp function
  let decoded := zfGraphFunction hf
  let values : Fin n → RankDomain lambda :=
    fun i => rankMember range (decoded (finZFSetEquiv n i)).val (decoded (finZFSetEquiv n i)).property
  refine ⟨values, Subtype.ext ?_⟩
  change zfFunctionGraph (rankAssignmentFunction hl values) = graph.val
  rw [← zfFunctionGraph_recovered hf]
  apply zfFunctionGraph_congr
  intro a
  change (decoded (finZFSetEquiv n ((finZFSetEquiv n).symm a))).val = (decoded a).val
  rw [Equiv.apply_symm_apply]

end FullMarkedBLP
