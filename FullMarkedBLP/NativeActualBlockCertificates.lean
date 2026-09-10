import FullMarkedBLP.NativeTopCertificates

namespace FullMarkedBLP

theorem rankRealization_native_actual_block_certificates {lambda : Ordinal.{u}} {a b : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (hReal : RankRowRealization a theta embedding)
    {r p e : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hp : row.p = some p) (he : row.e = some e)
    (hn : native a r = some (b, sources)) (hne : sources ≠ []) :
    ∃ block, nativeBlock row r sources = some block ∧
      BlockRankCertificates b
        (nativeColumnValues theta (nativeFreshValues theta (embedding r) r sources) r sources.length)
        (nativeEmbeddingValues embedding r sources.length) (embedding r) block := by
  have valid := hReal.valid
  have hm := hReal.proper r row hr
  have h := native_sources_of_success hn
  have hv := valid r row hr
  cases sources with
  | nil => contradiction
  | cons s ss =>
    have hne : s :: ss ≠ [] := by simp
    have helig := nativeSources_nonempty_eligible hr h hne
    have hstep : 2 ≤ row.step := by
      have hp := hv.2.2.2.1
      by_cases he : row.step = 1
      · have hh := nativeSources_step_one_empty hv hr he
        have := Option.some.inj (h.symm.trans hh)
        contradiction
      · omega
    have htop := nativeTop_actual_coreValid valid hr h
    have htopMarks := nativeTop_actual_properMarks valid hr hm h
    have htraces := rankRealization_native_top_certificates hReal hr hp he hn hne
    have htoplen := nativeTop_actual_length valid hr h
    have ht : ∀ x, r ≤ x → x ≤ r + (s :: ss).length →
        x ∈ (nativeTop row r (s :: ss)).core := by
      intro x hx hb
      apply (nativeTop_core_mem row r (s :: ss) x).mpr
      by_cases he : x = r
      · subst x; exact Or.inl (List.mem_of_getLast? hv.2.2.1)
      · exact Or.inr (Or.inr ⟨by omega, hb⟩)
    by_cases hmedium : row.core.length = 2 * row.step
    · obtain ⟨block, hb, hvalid⟩ := nativeBlockDown_medium_rankCertificates ss.length htop htopMarks htraces
        (by change _ = 2 * (row.step + (s :: ss).length); omega)
        (by change _ ≤ row.step + (s :: ss).length; simp; omega) ht
      exact ⟨block, by simpa [nativeBlock, hmedium] using hb, hvalid⟩
    · have hbool : (row.core.length == 2 * row.step) = false := by
        exact Bool.eq_false_iff.mpr (by simpa using hmedium)
      have hshort : row.core.length + 1 = 2 * row.step := by
        have hs := hv.2.2.2
        unfold Row.OrdinaryShape at hs
        rcases hs with ⟨hp, hs | hs | hs⟩ <;> omega
      have hsmin : 3 ≤ row.step := by
        have hs := hv.2.2.2
        unfold Row.OrdinaryShape at hs
        rcases hs with ⟨hp, hs | hs | hs⟩ <;> omega
      obtain ⟨block, hb, hvalid⟩ := nativeBlockDown_short_rankCertificates (s :: ss).length htop htopMarks htraces
        (by change _ = 2 * (row.step + (s :: ss).length); omega)
        (by change _ ≤ row.step + (s :: ss).length; omega) ht
      exact ⟨block, by simpa [nativeBlock, hbool] using hb, hvalid⟩


end FullMarkedBLP




