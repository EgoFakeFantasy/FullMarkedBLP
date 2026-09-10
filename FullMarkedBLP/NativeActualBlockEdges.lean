import FullMarkedBLP.NativeTopEdges

namespace FullMarkedBLP

theorem rankRealization_native_actual_block_edges {lambda : Ordinal.{u}} {a b : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (hReal : RankRowRealization a theta embedding)
    {r p e : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hp : row.p = some p) (he : row.e = some e)
    (hn : native a r = some (b, sources)) (hne : sources ≠ []) :
    ∃ block, nativeBlock row r sources = some block ∧
      BlockEdges (rankOrdinalAction (embedding r))
        (nativeColumnValues theta (nativeFreshValues theta (embedding r) r sources) r sources.length)
        r block := by
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
    have htraces := rankRealization_native_top_edges hReal hr hp he h hne
    rw [nativeEmbeddingValues_block embedding r (s :: ss).length (s :: ss).length (Nat.le_refl _)] at htraces
    have htoplen := nativeTop_actual_length valid hr h
    have ht := nativeTop_contains_targets hv (s :: ss)
    by_cases hmedium : row.core.length = 2 * row.step
    · obtain ⟨block, hb, hvalid⟩ := nativeBlockDown_medium_edges ss.length (rankOrdinalAction (embedding r)) _ htop htopMarks htraces
        (by change _ = 2 * (row.step + (s :: ss).length); omega)
        (by change _ ≤ row.step + (s :: ss).length; simp; omega) ht
      exact ⟨block, by simpa [nativeBlock, hmedium] using hb, hvalid⟩
    · have hbool : (row.core.length == 2 * row.step) = false := by
        exact Bool.eq_false_iff.mpr (by simpa using hmedium)
      obtain ⟨hshort, hsmin⟩ := Row.short_shape_of_eligible_ne_medium hv.2.2.2 helig hmedium
      obtain ⟨block, hb, hvalid⟩ := nativeBlockDown_short_edges (s :: ss).length (rankOrdinalAction (embedding r)) _ htop htopMarks htraces
        (by change _ = 2 * (row.step + (s :: ss).length); omega)
        (by change _ ≤ row.step + (s :: ss).length; omega) ht
      exact ⟨block, by simpa [nativeBlock, hbool] using hb, hvalid⟩


end FullMarkedBLP





