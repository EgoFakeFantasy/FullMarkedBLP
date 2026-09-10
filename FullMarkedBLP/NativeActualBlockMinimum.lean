import FullMarkedBLP.NativeBlockMinimum

namespace FullMarkedBLP

theorem rankRealization_native_actual_block_minimum {lambda : Ordinal.{u}} {a b : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (hReal : RankRowRealization a theta embedding)
    {r minimum : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hminimum : row.core.head? = some minimum)
    (hn : native a r = some (b, sources)) (hne : sources ≠ []) :
    ∃ block, nativeBlock row r sources = some block ∧
      BlockMinimum minimum block := by
  have valid := hReal.valid
  have hm := hReal.proper r row hr
  have h := native_sources_of_success hn
  have hv := valid r row hr
  cases sources with
  | nil => contradiction
  | cons s ss =>
    have hne : s :: ss ≠ [] := by simp
    have helig := nativeSources_nonempty_eligible hr h hne
    have hstep := nativeSources_nonempty_step_ge_two hv hr h hne
    have htop := nativeTop_actual_coreValid valid hr h
    have htopMarks := nativeTop_actual_properMarks valid hr hm h
    have htraces := nativeTop_preserves_minimum valid hr h hminimum
    have htoplen := nativeTop_actual_length valid hr h
    have ht := nativeTop_contains_targets hv (s :: ss)
    by_cases hmedium : row.core.length = 2 * row.step
    · obtain ⟨block, hb, hvalid⟩ := nativeBlockDown_medium_minimum ss.length htop htopMarks htraces
        (by change _ = 2 * (row.step + (s :: ss).length); omega)
        (by change _ ≤ row.step + (s :: ss).length; simp; omega) ht
      exact ⟨block, by simpa [nativeBlock, hmedium] using hb, hvalid⟩
    · have hbool : (row.core.length == 2 * row.step) = false := by
        exact Bool.eq_false_iff.mpr (by simpa using hmedium)
      obtain ⟨hshort, hsmin⟩ := Row.short_shape_of_eligible_ne_medium hv.2.2.2 helig hmedium
      obtain ⟨block, hb, hvalid⟩ := nativeBlockDown_short_minimum (s :: ss).length htop htopMarks htraces
        (by change _ = 2 * (row.step + (s :: ss).length); omega)
        (by change _ ≤ row.step + (s :: ss).length; omega) ht
      exact ⟨block, by simpa [nativeBlock, hbool] using hb, hvalid⟩


end FullMarkedBLP





