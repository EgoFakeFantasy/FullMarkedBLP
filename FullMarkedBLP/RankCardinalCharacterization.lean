import FullMarkedBLP.RankBijectionCardinal

namespace FullMarkedBLP

theorem ordinal_cardinal_iff_no_smaller_equinumerous (o : Ordinal.{u}) :
    (∃ c : Cardinal.{u}, c.ord = o) ↔ ∀ a < o, a.card ≠ o.card := by
  constructor
  · rintro ⟨c, rfl⟩ a ha
    simpa only [Cardinal.card_ord] using (Cardinal.lt_ord.mp ha).ne
  · intro h
    refine ⟨o.card, ?_⟩
    apply le_antisymm (Cardinal.ord_card_le o)
    by_contra hn
    have ht : o.card.ord < o := lt_of_not_ge hn
    exact h _ ht (Cardinal.card_ord o.card)

theorem ordinal_cardinal_iff_no_rank_bijection {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) (o : OrdinalDomain lambda) :
    (∃ c : Cardinal.{u}, c.ord = o.val) ↔
      ∀ a : OrdinalDomain lambda, a < o →
        ¬ ∃ f : RankDomain lambda,
          rankIsBijection f (ordinalDomainElement a) (ordinalDomainElement o) := by
  rw [ordinal_cardinal_iff_no_smaller_equinumerous]
  constructor
  · intro h a ha
    rw [rankBijection_exists_iff_card_eq hl]
    simpa only [ordinalDomainElement, Ordinal.card_toZFSet] using h a.val ha
  · intro h a ha
    let a' : OrdinalDomain lambda := ⟨a, ha.trans o.property⟩
    have hh := h a' ha
    rw [rankBijection_exists_iff_card_eq hl] at hh
    simpa only [ordinalDomainElement, Ordinal.card_toZFSet, a'] using hh

end FullMarkedBLP
