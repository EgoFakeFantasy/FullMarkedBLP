import FullMarkedBLP.RankInitialFormula

namespace FullMarkedBLP

theorem rankNoMemberBijection_ordinal_iff {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) (o : OrdinalDomain lambda) :
    rankNoMemberBijection (ordinalDomainElement o) ↔ ∃ c : Cardinal.{u}, c.ord = o.val := by
  rw [ordinal_cardinal_iff_no_rank_bijection hl o]
  constructor
  · intro h a ha
    exact h (ordinalDomainElement a) (Ordinal.toZFSet_mem_toZFSet_iff.mpr ha)
  · intro h a ha
    obtain ⟨b, hb, he⟩ := Ordinal.mem_toZFSet_iff.mp ha
    let b' : OrdinalDomain lambda := ⟨b, hb.trans o.property⟩
    have he' : ordinalDomainElement b' = a := Subtype.ext he
    rw [← he']
    exact h b' hb

theorem rankOrdinalAction_cardinal_iff {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) (j : RankElementaryEmbedding lambda) (o : OrdinalDomain lambda) :
    (∃ c : Cardinal.{u}, c.ord = (rankOrdinalAction j o).val) ↔
      ∃ c : Cardinal.{u}, c.ord = o.val := by
  rw [← rankNoMemberBijection_ordinal_iff hl, ← rankNoMemberBijection_ordinal_iff hl,
    ordinalDomainElement_action]
  exact rankElementary_noMemberBijection_iff j (ordinalDomainElement o)

theorem rankRealization_native_source_cardinals {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) {r : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hs : nativeSources a r = some sources) :
    ∀ x ∈ sources, ∃ c : Cardinal.{u}, c.ord = (rankOrdinalAction (embedding r) (theta x)).val := by
  intro x hx
  apply (rankOrdinalAction_cardinal_iff hl (embedding r) (theta x)).mpr
  have hb := nativeSources_below_owner h.valid hr hs x hx
  have hrb := (rowAt_bounds hr).2
  exact h.cardinals x (by omega)

theorem rankRealization_native_all_cardinals {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {a b : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) {r : Nat} {sources : List Nat}
    (hn : native a r = some (b, sources)) :
    ∀ i, i ≤ b.length + 1 → ∃ c : Cardinal.{u}, c.ord =
      (nativeColumnValues theta (nativeFreshValues theta (embedding r) r sources) r sources.length i).val := by
  apply (rankRealization_native_cardinals_iff h hn).mpr
  obtain ⟨row, hr, _⟩ := Option.bind_eq_some_iff.mp hn
  exact rankRealization_native_source_cardinals hl h hr (native_sources_of_success hn)

end FullMarkedBLP

