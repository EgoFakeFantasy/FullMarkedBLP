import FullMarkedBLP.RankCofinalContinuity
import FullMarkedBLP.RankCriticalInaccessible

namespace FullMarkedBLP

/-- Natural numbers as the ordinal members of omega, in any set universe. -/
noncomputable def natOrdinalOmegaEquiv : Nat ≃ Set.Iio Ordinal.omega0.{u} :=
  Equiv.ofBijective (fun n => ⟨(n : Ordinal.{u}), Ordinal.natCast_lt_omega0 n⟩) (by
    constructor
    · intro m n same
      exact Nat.cast_injective (congrArg Subtype.val same)
    · intro a
      obtain ⟨n, eq⟩ := Ordinal.lt_omega0.mp a.property
      exact ⟨n, Subtype.ext eq.symm⟩)

/-- Actual elementary embeddings are continuous along countable cofinal
sequences below their domain height. Fixedness of the indexing set omega
and of its members is proved, not supplied as an extra hypothesis. -/
theorem rankOrdinalAction_cofinal_nat {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {j : RankElementaryEmbedding lambda}
    {critical : OrdinalDomain lambda} (cp : RankCriticalPoint j critical)
    (beta : OrdinalDomain lambda) (f : Nat → Set.Iio beta.val)
    (cofinal : ∀ b < beta.val, ∃ n, b < (f n).val) :
    ∀ b < (rankOrdinalAction j beta).val, ∃ n : Nat,
      b < (rankOrdinalAction j ⟨(f n).val, (f n).property.trans beta.property⟩).val := by
  have omegaBelow := rankCriticalPoint_omega_lt hl cp
  let omegaDomain : OrdinalDomain lambda := ⟨Ordinal.omega0, omegaBelow.trans critical.property⟩
  let indexed : Set.Iio omegaDomain.val → Set.Iio beta.val := fun a => f (natOrdinalOmegaEquiv.symm a)
  have indexedCofinal : ∀ b < beta.val, ∃ a, b < (indexed a).val := by
    intro b hb
    obtain ⟨n, hn⟩ := cofinal b hb
    refine ⟨natOrdinalOmegaEquiv n, ?_⟩
    simpa only [indexed, Equiv.symm_apply_apply] using hn
  have fixedDomain : j (ordinalDomainElement omegaDomain) = ordinalDomainElement omegaDomain := by
    rw [← ordinalDomainElement_action, rankOrdinalAction_omega]
  have fixedMembers : ∀ x : RankDomain lambda,
      x.val ∈ (ordinalDomainElement omegaDomain).val → j x = x := by
    intro x hx
    apply rankCriticalPoint_fixes_rank hl cp
    have below : x.val.rank < Ordinal.omega0 := by
      simpa only [omegaDomain, ordinalDomainElement, Ordinal.rank_toZFSet] using ZFSet.rank_lt_of_mem hx
    exact below.trans omegaBelow
  have image := rankOrdinalAction_cofinal_of_fixed_domain hl j omegaDomain beta indexed
    indexedCofinal fixedDomain fixedMembers
  intro b hb
  obtain ⟨a, ha⟩ := image b hb
  exact ⟨natOrdinalOmegaEquiv.symm a, ha⟩

end FullMarkedBLP
