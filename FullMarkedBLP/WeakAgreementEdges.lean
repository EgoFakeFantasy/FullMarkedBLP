import FullMarkedBLP.CutoffMinimum

namespace FullMarkedBLP

/-- A strict initial segment distinguishes every element below its boundary,
    even from a comparison element not known to lie below that boundary. -/
theorem eq_of_bounded_lower_sections {O : Type u} (lt : O → O → Prop)
    (irrefl : ∀ x, ¬lt x x) (trans : ∀ {x y z}, lt x y → lt y z → lt x z)
    (compare : ∀ x y, x = y ∨ lt x y ∨ lt y x)
    {a b delta : O} (ha : lt a delta)
    (h : ∀ x, lt x delta → (lt x a ↔ lt x b)) : a = b := by
  rcases compare a b with he | hab | hba
  · exact he
  · exact False.elim (irrefl a ((h a ha).mpr hab))
  · exact False.elim (irrefl b ((h b (trans hba ha)).mp hba))

/-- Reading a bounded ordinal image from weak membership agreement does not
    require assuming that the other image is below the cutoff. -/
theorem cutoffAgreement_ordinal_image {V : Type u} {O : Type v}
    (mem : V → V → Prop) (below : O → V → Prop) (ord : O → V)
    (lt : O → O → Prop)
    (irrefl : ∀ x, ¬lt x x) (trans : ∀ {x y z}, lt x y → lt y z → lt x z)
    (compare : ∀ x y, x = y ∨ lt x y ∨ lt y x)
    (ordinalMem : ∀ x y, mem (ord x) (ord y) ↔ lt x y)
    (ordinalBelow : ∀ delta x, lt x delta → below delta (ord x))
    {f g : V → V} {delta a b : O} {z : V}
    (h : cutoffAgreement mem below delta f g) (hz : below delta z)
    (hf : f z = ord a) (hg : g z = ord b) (ha : lt a delta) : a = b := by
  apply eq_of_bounded_lower_sections lt irrefl trans compare ha
  intro x hx
  have hm := h (ord x) z (ordinalBelow delta x hx) hz
  rw [hf, hg] at hm
  exact (ordinalMem x a).symm.trans (hm.trans (ordinalMem x b))

theorem cutoffAgreement_reads_edge {V : Type u} {O : Type v}
    (mem : V → V → Prop) (below : O → V → Prop) (ord : O → V)
    (lt : O → O → Prop)
    (irrefl : ∀ x, ¬lt x x) (trans : ∀ {x y z}, lt x y → lt y z → lt x z)
    (compare : ∀ x y, x = y ∨ lt x y ∨ lt y x)
    (ordinalMem : ∀ x y, mem (ord x) (ord y) ↔ lt x y)
    (ordinalBelow : ∀ delta x, lt x delta → below delta (ord x))
    {f g : V → V} {delta target : O} {z : V}
    (h : cutoffAgreement mem below delta f g) (hz : below delta z)
    (hf : f z = ord target) (hg : ∃ other, g z = ord other)
    (ht : lt target delta) : g z = ord target := by
  obtain ⟨other, ho⟩ := hg
  have he := cutoffAgreement_ordinal_image mem below ord lt irrefl trans compare
    ordinalMem ordinalBelow h hz hf ho ht
  simpa only [← he] using ho

/-- A visible moved ordinal remains moved under weak agreement even when its
    image is beyond the cutoff. This is the critical-point transfer mechanism. -/
theorem cutoffAgreement_moves_ordinal {V : Type u} {O : Type v}
    (mem : V → V → Prop) (below : O → V → Prop) (ord : O → V)
    (lt : O → O → Prop) (irrefl : ∀ x, ¬lt x x)
    (ordinalMem : ∀ x y, mem (ord x) (ord y) ↔ lt x y)
    (ordinalBelow : ∀ delta x, lt x delta → below delta (ord x))
    {f g : V → V} {delta c image : O}
    (h : cutoffAgreement mem below delta f g) (hc : lt c delta)
    (hf : f (ord c) = ord image) (hmoves : lt c image) : g (ord c) ≠ ord c := by
  intro hfix
  have hmem : mem (ord c) (f (ord c)) := by
    rw [hf]
    exact (ordinalMem c image).mpr hmoves
  have hg := (h (ord c) (ord c) (ordinalBelow delta c hc) (ordinalBelow delta c hc)).mp hmem
  rw [hfix] at hg
  exact irrefl c ((ordinalMem c c).mp hg)

theorem cutoffAgreement_critical_below {V : Type u} {O : Type v}
    (mem : V → V → Prop) (below : O → V → Prop) (ord : O → V)
    (lt : O → O → Prop)
    (irrefl : ∀ x, ¬lt x x) (trans : ∀ {x y z}, lt x y → lt y z → lt x z)
    (compare : ∀ x y, x = y ∨ lt x y ∨ lt y x)
    (ordinalMem : ∀ x y, mem (ord x) (ord y) ↔ lt x y)
    (ordinalBelow : ∀ delta x, lt x delta → below delta (ord x))
    {f g : V → V} {delta c image critical bound : O}
    (h : cutoffAgreement mem below delta f g) (hc : lt c delta)
    (hf : f (ord c) = ord image) (hmoves : lt c image)
    (hfix : ∀ x, lt x critical → g (ord x) = ord x)
    (hbound : lt c bound) : lt critical bound := by
  have hm := cutoffAgreement_moves_ordinal mem below ord lt irrefl ordinalMem ordinalBelow h hc hf hmoves
  rcases compare critical c with he | hlt | hgt
  · simpa only [he] using hbound
  · exact trans hlt hbound
  · exact False.elim (hm (hfix c hgt))

end FullMarkedBLP

