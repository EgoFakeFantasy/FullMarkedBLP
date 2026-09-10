import FullMarkedBLP.CopyMarks

namespace FullMarkedBLP

theorem copiedRow_marks_sorted {a : Pattern} {last row copied : Row} {source : Nat}
    (hv : last.CoreValid a.length) (hr : row.CoreValid source)
    (h : copiedRow a last source row = some copied) : copied.marks.Pairwise (· < ·) := by
  obtain ⟨core, hc, h⟩ := Option.bind_eq_some_iff.mp h
  cases Option.some.inj h
  have hs := copiedCore_sorted hv hr hc
  apply List.pairwise_filterMap.mpr
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij x hx y hy
  dsimp only at hx hy

  split at hx
  next hix =>
    split at hy
    next hjy =>
      have hxe := Option.some.inj hx
      have hye := Option.some.inj hy
      have hci : i < core.length := by simp at hi; omega
      have hcj : j < core.length := by simp at hj; omega
      have hh := List.pairwise_iff_getElem.mp hs i j hci hcj hij
      simp only [List.get_eq_getElem, List.getElem_zipIdx, List.getElem_zip] at hxe hye
      simpa only [hxe, hye] using hh
    next => simp at hy
  next => simp at hx

theorem copiedRow_properMarks {a : Pattern} {last row copied : Row} {source owner : Nat}
    (hv : last.CoreValid a.length) (hr : row.CoreValid source) (hm : row.ProperMarks source)
    (howner : copyEntry a.length last source = some owner)
    (h : copiedRow a last source row = some copied) : copied.ProperMarks owner :=
  ⟨copiedRow_marks_sorted hv hr h, fun _ hx => copiedRow_mark_position hv hr hm howner h hx⟩

end FullMarkedBLP




