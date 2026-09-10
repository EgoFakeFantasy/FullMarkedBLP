import FullMarkedBLP.RankSteelImageCut
import FullMarkedBLP.RankSteelBounds

namespace FullMarkedBLP

theorem ZFOrdinalCollection.relation_equivShrink (s : ZFOrdinalCollection.{u}) (a b : s.carrier) :
    s.relation (equivShrink s.carrier a) (equivShrink s.carrier b) ↔ a.val ∈ b.val := by
  change ((equivShrink s.carrier).symm (equivShrink s.carrier a)).val.rank <
    ((equivShrink s.carrier).symm (equivShrink s.carrier b)).val.rank ↔ _
  simp only [Equiv.symm_apply_apply]
  exact (s.ordinal _ a.property).rank_lt_iff_mem (s.ordinal _ b.property)

theorem ZFOrdinalCollection.orderType_lt_of_embedding_below (s t : ZFOrdinalCollection.{u})
    (cut : t.carrier) (f : s.carrier → t.carrier)
    (ordered : ∀ a b, a.val ∈ b.val → (f a).val ∈ (f b).val)
    (below : ∀ a, (f a).val ∈ cut.val) : s.orderType < t.orderType := by
  let point := equivShrink t.carrier cut
  let map : Shrink.{u} s.carrier → {b : Shrink.{u} t.carrier // t.relation b point} :=
    fun a => ⟨equivShrink t.carrier (f ((equivShrink s.carrier).symm a)),
      (t.relation_equivShrink _ cut).mpr (below _)⟩
  let embedding : s.relation ↪r Subrel t.relation (fun b => t.relation b point) :=
    RelEmbedding.ofMonotone map (by
      intro a b related
      change t.relation (equivShrink t.carrier (f ((equivShrink s.carrier).symm a)))
        (equivShrink t.carrier (f ((equivShrink s.carrier).symm b)))
      apply (t.relation_equivShrink _ _).mpr
      apply ordered
      apply (s.relation_equivShrink _ _).mp
      simpa only [Equiv.apply_symm_apply] using related)
  exact embedding.ordinal_type_le.trans_lt (PrincipalSeg.ofElement t.relation point).ordinal_type_lt

/-- Application strictly decreases the Steel order type at a fixed
critical inaccessible gamma whenever the outer critical point is below it. -/
theorem rankSteelOrderType_apply_lt {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j k : RankElementaryEmbedding lambda)
    {owner : RankElementaryEmbedding lambda} {gamma critical : OrdinalDomain lambda}
    (cpGamma : RankCriticalPoint owner gamma) (cp : RankCriticalPoint j critical)
    (below : critical < gamma) :
    rankSteelOrderType hl (rankApply hl j k) gamma < rankSteelOrderType hl j gamma := by
  obtain ⟨alpha, alphaSmall, crosses⟩ := rankOrdinalAction_crosses_bound hl cp gamma below
  obtain ⟨cut, h, cutMember, ordered, values⟩ := rankSteelImageCut_exists hl j k alpha cpGamma alphaSmall crosses
  let child := rankSteelHull hl (rankApply hl j k) gamma
  let parent := rankSteelHull hl j gamma
  have witness : ∀ a : child.val, ∃ b : parent.val, b.val ∈ cut.val ∧
      rankGraphApplies h (rankMember child a.val a.property) (rankMember parent b.val b.property) := by
    intro a
    obtain ⟨value, member, small, edge⟩ := values (rankMember child a.val a.property) a.property
    exact ⟨⟨value.val, member⟩, small, edge⟩
  let map : child.val → parent.val := fun a => Classical.choose (witness a)
  have spec (a : child.val) : (map a).val ∈ cut.val ∧
      rankGraphApplies h (rankMember child a.val a.property)
        (rankMember parent (map a).val (map a).property) := Classical.choose_spec (witness a)
  apply (rankSteelHullCollection hl (rankApply hl j k) gamma).orderType_lt_of_embedding_below
    (rankSteelHullCollection hl j gamma) ⟨cut.val, cutMember⟩ map
  · intro a b member
    exact (ordered _ _ _ _ (spec a).2 (spec b).2).mp member
  · exact fun a => (spec a).1

end FullMarkedBLP
