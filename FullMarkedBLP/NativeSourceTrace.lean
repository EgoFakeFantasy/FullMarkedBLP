import FullMarkedBLP.NativeSourceRank

namespace FullMarkedBLP

/-- Literal replacement-block lookup in the complete native output. -/
theorem native_block_rowAt {a : Pattern} {r : Nat} {row : Row}
    {sources : List Nat} {block : Pattern}
    (hr : rowAt a r = some row)
    {j : Nat} (hj : j < block.length) :
    rowAt (a.take (r - 1) ++ block ++
      (a.drop r).map (Row.shiftAfter r sources.length)) (r + j) = block[j]? := by
  have hrb := rowAt_bounds hr
  have hpre : (a.take (r - 1)).length = r - 1 := by simp; omega
  simp only [rowAt, show r + j ≠ 0 by omega, ↓reduceIte, List.append_assoc]
  rw [List.getElem?_append_right (by omega : (a.take (r - 1)).length ≤ r + j - 1)]
  have he : r + j - 1 - (a.take (r - 1)).length = j := by omega
  rw [he, List.getElem?_append_left hj]

/-- Every inserted source is reached by one p-step from its new row. -/
theorem native_source_predecessor {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r x : Nat} {sources : List Nat}
    (hn : native a r = some (b, sources)) (hx : x ∈ sources) :
    predecessor b (r + ((sources.filter (· < x)).length + 1)) = some x := by
  obtain ⟨row, hr, hn⟩ := Option.bind_eq_some_iff.mp hn
  obtain ⟨ss, hs, hn⟩ := Option.bind_eq_some_iff.mp hn
  obtain ⟨block, hb, hn⟩ := Option.bind_eq_some_iff.mp hn
  change some (_, ss) = some (b, sources) at hn
  cases Option.some.inj hn
  have hv := valid r row hr
  have hl := Row.step_lt_length hv.2.2.2
  obtain ⟨p, hp⟩ := fromRight_exists (xs := row.core) (k := row.step + 1) (by omega) (by omega)
  obtain ⟨e, he⟩ := fromRight_exists (xs := row.core) (k := row.step) hv.2.2.2.1 (by omega)
  have hp' : row.p = some p := hp
  have he' : row.e = some e := he
  have hlt : (sources.filter (· < x)).length < sources.length :=
    List.length_filter_lt_length_iff_exists.mpr ⟨x, hx, by simp⟩
  have hlen := nativeBlock_length hb
  have hi : (sources.filter (· < x)).length + 1 < block.length := by omega
  unfold predecessor
  rw [native_block_rowAt hr hi]
  exact nativeBlock_source_p valid hr hp' he' hs hx hb

theorem native_source_trace {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r x : Nat} {sources : List Nat}
    (hn : native a r = some (b, sources)) (hx : x ∈ sources) :
    Trace b x (r + ((sources.filter (· < x)).length + 1))
      [r + ((sources.filter (· < x)).length + 1), x] := by
  have hp := native_source_predecessor valid hn hx
  have hv := native_preserves_coreValid valid hn
  exact Trace.next (predecessor_lt hv hp) hp Trace.stop

end FullMarkedBLP


