import FullMarkedBLP.RankOrdinalCofinalGraph
import FullMarkedBLP.RankPairPreservation
import FullMarkedBLP.OrdinalAction

namespace FullMarkedBLP

/-- A cofinal function indexed by a fixed ordinal with fixed members remains
cofinal after applying j pointwise to its values. The proof transfers the
actual function graph and its first-order cofinality predicate. -/
theorem rankOrdinalAction_cofinal_of_fixed_domain {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) (j : RankElementaryEmbedding lambda)
    (alpha beta : OrdinalDomain lambda) (f : Set.Iio alpha.val → Set.Iio beta.val)
    (cofinal : ∀ b < beta.val, ∃ a, b < (f a).val)
    (fixedDomain : j (ordinalDomainElement alpha) = ordinalDomainElement alpha)
    (fixedMembers : ∀ x : RankDomain lambda,
      x.val ∈ (ordinalDomainElement alpha).val → j x = x) :
    ∀ b < (rankOrdinalAction j beta).val, ∃ a : Set.Iio alpha.val,
      b < (rankOrdinalAction j ⟨(f a).val, (f a).property.trans beta.property⟩).val := by
  let graph := rankOrdinalFunctionGraph hl alpha beta f
  have function := (rankElementary_function_iff j graph _ _).mpr
    (rankOrdinalFunctionGraph_isFunction hl alpha beta f)
  have imageCofinal := (rankElementary_cofinal_iff j graph _ _).mpr
    (rankOrdinalFunctionGraph_cofinal hl alpha beta f cofinal)
  intro b hb
  let argument := ordinalDomainElement (⟨b, hb.trans (rankOrdinalAction j beta).property⟩ : OrdinalDomain lambda)
  have member : argument.val ∈ (j (ordinalDomainElement beta)).val := by
    rw [rankOrdinalAction_compat]
    exact Ordinal.toZFSet_mem_toZFSet_iff.mpr hb
  obtain ⟨x, hx, y, _, imageEdge, above⟩ := imageCofinal argument member
  have oldMember : x.val ∈ (ordinalDomainElement alpha).val := by simpa only [fixedDomain] using hx
  obtain ⟨aOrdinal, below, eqX⟩ := Ordinal.mem_toZFSet_iff.mp oldMember
  let a : Set.Iio alpha.val := ⟨aOrdinal, below⟩
  let oldY := ordinalDomainElement (⟨(f a).val, (f a).property.trans beta.property⟩ : OrdinalDomain lambda)
  have sameX : ordinalDomainElement (⟨a.val, a.property.trans alpha.property⟩ : OrdinalDomain lambda) = x :=
    Subtype.ext eqX
  have oldEdge : rankGraphApplies graph x oldY := by
    rw [← sameX]
    exact rankOrdinalFunctionGraph_applies hl alpha beta f a
  have mappedEdge : rankGraphApplies (j graph) x (j oldY) := by
    rw [← fixedMembers x oldMember, rankGraphApplies_iff hl]
    exact (rankElementary_graph_membership_iff hl j x oldY graph).mpr
      ((rankGraphApplies_iff hl _ _ _).mp oldEdge)
  obtain ⟨z, _, _, unique⟩ := function.2 x hx
  have sameY : y = j oldY := (unique _ imageEdge).trans (unique _ mappedEdge).symm
  rw [sameY] at above
  refine ⟨a, ?_⟩
  change b.toZFSet ∈ (j (ordinalDomainElement _)).val at above
  rw [rankOrdinalAction_compat] at above
  exact Ordinal.toZFSet_mem_toZFSet_iff.mp above

end FullMarkedBLP
