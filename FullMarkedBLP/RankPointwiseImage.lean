import FullMarkedBLP.RankSequenceGraph
import FullMarkedBLP.RankBijectionCardinal

namespace FullMarkedBLP

noncomputable def rankPointwiseImage {lambda : Ordinal.{u}}
    (j : RankElementaryEmbedding lambda) (x : RankDomain lambda) : RankDomain lambda :=
  ⟨ZFSet.range (fun a : x.val => (j (rankMember x a.val a.property)).val), by
    apply (ZFSet.rank_mono (show ZFSet.range (fun a : x.val => (j (rankMember x a.val a.property)).val) ⊆
      (j x).val from ?_)).trans_lt (j x).property
    intro y hy
    obtain ⟨a, rfl⟩ := ZFSet.mem_range.mp hy
    exact (rankElementary_mem_iff j _ x).mpr a.property⟩

theorem rankPointwiseImage_subset {lambda : Ordinal.{u}}
    (j : RankElementaryEmbedding lambda) (x : RankDomain lambda) :
    (rankPointwiseImage j x).val ⊆ (j x).val := by
  intro y hy
  obtain ⟨a, rfl⟩ := ZFSet.mem_range.mp hy
  exact (rankElementary_mem_iff j _ x).mpr a.property

theorem rankPointwiseImage_mem {lambda : Ordinal.{u}}
    (j : RankElementaryEmbedding lambda) (x : RankDomain lambda) (y : ZFSet.{u}) :
    y ∈ (rankPointwiseImage j x).val ↔
      ∃ a : x.val, (j (rankMember x a.val a.property)).val = y := ZFSet.mem_range

theorem rankPointwiseImage_card_eq {lambda : Ordinal.{u}}
    (j : RankElementaryEmbedding lambda) (x : RankDomain lambda) :
    (rankPointwiseImage j x).val.card = x.val.card := by
  let function : x.val → (rankPointwiseImage j x).val := fun a =>
    ⟨(j (rankMember x a.val a.property)).val, ZFSet.mem_range.mpr ⟨a, rfl⟩⟩
  have bijective : Function.Bijective function := by
    constructor
    · intro a b same
      have imageEq : j (rankMember x a.val a.property) = j (rankMember x b.val b.property) :=
        Subtype.ext (congrArg (fun y : (rankPointwiseImage j x).val => y.val) same)
      exact Subtype.ext (congrArg (fun y : RankDomain lambda => y.val) (j.injective imageEq))
    · intro y
      obtain ⟨a, ha⟩ := (rankPointwiseImage_mem j x y.val).mp y.property
      exact ⟨a, Subtype.ext ha⟩
  have cards := Cardinal.mk_congr (Equiv.ofBijective function bijective)
  have eq : x.val.card = (rankPointwiseImage j x).val.card := by
    simpa only [ZFSet.cardinalMk_coe_sort, Cardinal.lift_inj] using cards
  exact eq.symm

end FullMarkedBLP
