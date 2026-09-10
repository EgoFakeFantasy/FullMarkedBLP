import FullMarkedBLP.NativeBottomBound

namespace FullMarkedBLP

theorem native_suffix_sat_witness {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {owner r p e : Nat} {row : Row} {sources : List Nat}
    (hn : native a owner = some (b, sources))
    (hr : rowAt a r = some row) (howner : owner < r)
    (hp : row.p = some p) (he : row.e = some e)
    (hw : ∃ er v, rowAt a e = some er ∧ er.b = some v ∧ v ≤ p) :
    ∃ out er v, rowAt b (r + sources.length) = some out ∧
      out.p = some (shiftAfter owner sources.length p) ∧
      out.e = some (shiftAfter owner sources.length e) ∧
      rowAt b (shiftAfter owner sources.length e) = some er ∧
      er.b = some v ∧ v ≤ shiftAfter owner sources.length p := by
  by_cases heq : e = owner
  · subst e
    obtain ⟨old, v, hold, hb, hle⟩ := hw
    have hsrc := native_sources_of_success hn
    by_cases hnil : sources = []
    · subst sources
      have hi := native_empty hold hsrc
      have hab := (Prod.mk.inj (Option.some.inj (hn.symm.trans hi))).1
      subst b
      refine ⟨row, old, v, by simpa using hr, ?_, ?_, ?_, hb, ?_⟩
      · simpa [shiftAfter] using hp
      · simpa [shiftAfter] using he
      · simpa [shiftAfter] using hold
      · simpa [shiftAfter] using hle
    · have hbounds := rowAt_bounds hold
      have hlen := native_length hn
      obtain ⟨bottom, hbottom⟩ := rowAt_exists (a := b) hbounds.1 (by omega)
      have hvbottom := native_preserves_coreValid valid hn owner bottom hbottom
      obtain ⟨v', hb'⟩ := Row.b_exists hvbottom
      have hbound := native_bottom_b_le valid hold hn hnil hbottom hb hb'
      have hout : rowAt b (r + sources.length) = some (row.shiftAfter owner sources.length) := by
        simpa only [hr, Option.map_some] using native_suffix_rowAt hn howner
      refine ⟨_, bottom, v', hout, ?_, ?_, ?_, hb', ?_⟩
      · simp only [shifted_row_p, hp, Option.map_some]
      · simp only [shifted_row_e, he, Option.map_some]
      · simpa [shiftAfter] using hbottom
      · have hps : p ≤ shiftAfter owner sources.length p := by unfold shiftAfter; split <;> omega
        omega
  · exact native_suffix_sat_away_owner valid hn hr howner hp he heq hw

theorem native_sat_nonempty_of_others {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r : Nat} {sources : List Nat}
    (hs : ∀ i row, i ≠ r → rowAt a i = some row → row.core.length ≤ 2 * row.step →
      ∃ p e er v, row.p = some p ∧ row.e = some e ∧ rowAt a e = some er ∧ er.b = some v ∧ v ≤ p)
    (hn : native a r = some (b, sources)) (hne : sources ≠ []) : Sat b := by
  obtain ⟨old, hold, _⟩ := Option.bind_eq_some_iff.mp hn
  have hsrc := native_sources_of_success hn
  have hv := valid r old hold
  have hroom := Row.step_lt_length hv.2.2.2
  obtain ⟨p, hp⟩ := fromRight_exists (xs := old.core) (k := old.step + 1) (by omega) (by omega)
  obtain ⟨e, he⟩ := fromRight_exists (xs := old.core) (k := old.step) hv.2.2.2.1 (by omega)
  intro i row hi heligible
  by_cases hbefore : i < r
  · have ha : rowAt a i = some row := (native_prefix_rowAt hn hbefore).symm.trans hi
    obtain ⟨q, ep, er, v, hq, hep, her, hb, hle⟩ := hs i row (by omega) ha heligible
    have hvrow := valid i row ha
    have hepbound := fromRight_le_last hvrow.1 hvrow.2.2.1 hvrow.2.2.2.1 hep
    exact ⟨q, ep, er, v, hq, hep, (native_prefix_rowAt hn (by omega)).trans her, hb, hle⟩
  · by_cases hin : i ≤ r + sources.length
    · have hj : i - r ≤ sources.length := by omega
      obtain ⟨out, q, ep, er, v, hout, hq, hep, her, hb, hle⟩ := native_block_sat_witness valid hold hp he hsrc hne hn hj
      have hout' : rowAt b i = some out := by simpa only [show r + (i - r) = i by omega] using hout
      have heq := Option.some.inj (hout'.symm.trans hi)
      subst out
      exact ⟨q, ep, er, v, hq, hep, her, hb, hle⟩
    · have hbounds := rowAt_bounds hi
      have hlen := native_length hn
      have hpos : 0 < i - sources.length := by omega
      obtain ⟨original, horig⟩ := rowAt_exists (a := a) hpos (by omega)
      have hsuffix := native_suffix_rowAt hn (by omega : r < i - sources.length)
      have hlookup : rowAt b i = some (original.shiftAfter r sources.length) := by
        simpa only [show i - sources.length + sources.length = i by omega, horig, Option.map_some] using hsuffix
      have heq := Option.some.inj (hlookup.symm.trans hi)
      subst row
      have helig : original.core.length ≤ 2 * original.step := by simpa [Row.shiftAfter] using heligible
      obtain ⟨q, ep, er, v, hq, hep, her, hb, hle⟩ := hs _ original (by omega) horig helig
      obtain ⟨out, er', v', hout, hq', hep', her', hb', hle'⟩ := native_suffix_sat_witness valid hn horig (by omega) hq hep ⟨er, v, her, hb, hle⟩
      have hout' : rowAt b i = some out := by simpa only [show i - sources.length + sources.length = i by omega] using hout
      have heout := Option.some.inj (hout'.symm.trans hlookup)
      subst out
      exact ⟨_, _, er', v', hq', hep', her', hb', hle'⟩

end FullMarkedBLP

