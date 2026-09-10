import FullMarkedBLP.CopyProper
import FullMarkedBLP.NativeProperClosure

namespace FullMarkedBLP

theorem copiedRow_properMarks_shift {a : Pattern} {last row copied : Row} {source p : Nat}
    (hv : last.CoreValid a.length) (hr : row.CoreValid source) (hm : row.ProperMarks source)
    (hp : last.p = some p) (hsp : p ≤ source)
    (h : copiedRow a last source row = some copied) :
    copied.ProperMarks (source + (a.length - p)) := by
  obtain ⟨owner, ho, _⟩ := copiedRow_coreValid hv hr h
  have he := copyEntry_high_value hv hp hsp ho
  simpa only [he] using copiedRow_properMarks hv hr hm ho h

theorem copied_block_properMarks {a : Pattern} {last : Row} {sources : List Nat} {copied : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (marks : ∀ r row, rowAt a r = some row → row.ProperMarks r)
    (hv : last.CoreValid a.length) (hs : shortCopySources last = some sources)
    (h : sources.mapM (fun source => do
      let row ← rowAt a source
      copiedRow a last source row) = some copied) : BlockProperMarks a.length copied := by
  obtain ⟨p, e, hp, _, _, hsrc⟩ := shortCopySources_description hs
  have hpn := fromRight_le_last hv.1 hv.2.2.1 (by omega : 0 < last.step + 1) hp
  intro i hi
  have hget : copied[i]? = some copied[i] := by simp [hi]
  obtain ⟨source, hsource, hrow⟩ := (option_mapM_forall2 h).at hget
  have hsource' := hsource
  rw [hsrc] at hsource'
  obtain ⟨hb, hval⟩ := List.getElem?_eq_some_iff.mp hsource'
  have heq : p + i = source := by simpa using hval
  obtain ⟨row, hr, hc⟩ := Option.bind_eq_some_iff.mp hrow
  have hvalid := copiedRow_properMarks_shift hv (valid source row hr) (marks source row hr) hp (by omega) hc
  have hiEq : source + (a.length - p) = a.length + i := by omega
  simpa only [hiEq] using hvalid

theorem shortCopy_preserves_properMarks {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (marks : ∀ r row, rowAt a r = some row → row.ProperMarks r)
    (h : shortCopy a = some b) : ∀ r row, rowAt b r = some row → row.ProperMarks r := by
  unfold shortCopy at h
  split at h
  next => simp at h
  next hlen =>
    obtain ⟨last, hl, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨sources, hs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨copied, hc, h⟩ := Option.bind_eq_some_iff.mp h
    cases Option.some.inj h
    have hr : rowAt a a.length = some last := by
      simpa [rowAt, show a.length ≠ 0 by omega, List.getLast?_eq_getElem?] using hl
    have hb := copied_block_properMarks valid marks (valid a.length last hr) hs hc
    apply properMarks_iff_block.mpr
    apply blockProperMarks_append
    · simpa [List.dropLast_eq_take] using blockProperMarks_take (properMarks_iff_block.mp marks) (a.length - 1)
    · have he : 1 + a.dropLast.length = a.length := by simp; omega
      simpa only [he] using hb

end FullMarkedBLP



