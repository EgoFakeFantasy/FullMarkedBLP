import FullMarkedBLP.NativeMediumTargetBChain

namespace FullMarkedBLP

theorem nativeBlock_actual_target_b {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r : Nat} {row : Row} {sources : List Nat} {block : Pattern}
    (hr : rowAt a r = some row) (h : nativeSources a r = some sources)
    (hne : sources ≠ []) (hb : nativeBlock row r sources = some block) :
    ∀ j (hj : j < block.length), 0 < j → (block[j]).b = some (r + j - 1) := by
  have hv := valid r row hr
  have hroom := Row.step_lt_length hv.2.2.2
  cases sources with
  | nil => contradiction
  | cons s ss =>
    have helig := nativeSources_nonempty_eligible hr h hne
    have hstep := nativeSources_nonempty_step_ge_two hv hr h hne
    have htop := nativeTop_actual_coreValid valid hr h
    have htoplen := nativeTop_actual_length valid hr h
    have ht := nativeTop_contains_targets hv (s :: ss)
    by_cases hmedium : row.core.length = 2 * row.step
    · apply nativeBlockDown_medium_target_b ss.length htop
        (by change _ = 2 * (row.step + (s :: ss).length); omega)
        (by change _ ≤ row.step + (s :: ss).length; simp; omega) ht
      simpa [nativeBlock, hmedium] using hb
    · have hbool : (row.core.length == 2 * row.step) = false :=
        Bool.eq_false_iff.mpr (by simpa using hmedium)
      obtain ⟨hshort, hsmin⟩ := Row.short_shape_of_eligible_ne_medium hv.2.2.2 helig hmedium
      apply nativeBlockDown_short_target_b (s :: ss).length htop
        (by change _ = 2 * (row.step + (s :: ss).length); omega)
        (by change _ ≤ row.step + (s :: ss).length; omega) ht
      simpa [nativeBlock, hbool] using hb

end FullMarkedBLP

