import FullMarkedBLP.NativeTraceActual

namespace FullMarkedBLP

theorem native_suffix_rowAt {a b : Pattern} {r i : Nat} {sources : List Nat}
    (hn : native a r = some (b, sources)) (hi : r < i) :
    rowAt b (i + sources.length) = (rowAt a i).map (Row.shiftAfter r sources.length) := by
  obtain ⟨row, hr, hn⟩ := Option.bind_eq_some_iff.mp hn
  obtain ⟨ss, hs, hn⟩ := Option.bind_eq_some_iff.mp hn
  obtain ⟨block, hb, hn⟩ := Option.bind_eq_some_iff.mp hn
  change some (_, ss) = some (b, sources) at hn
  cases Option.some.inj hn
  have hrb := rowAt_bounds hr
  have hpre : (a.take (r - 1)).length = r - 1 := by simp; omega
  have hlen := nativeBlock_length hb
  have hpref : (a.take (r - 1) ++ block).length = r + sources.length := by
    simp only [List.length_append, hpre, hlen]; omega
  simp only [rowAt, show i + sources.length ≠ 0 by omega,
    show i ≠ 0 by omega, ↓reduceIte]
  rw [List.getElem?_append_right (by omega :
    (a.take (r - 1) ++ block).length ≤ i + sources.length - 1)]
  have he : i + sources.length - 1 - (a.take (r - 1) ++ block).length = i - 1 - r := by omega
  rw [he]
  simp only [List.getElem?_map, List.getElem?_drop]
  have he' : r + (i - 1 - r) = i - 1 := by omega
  rw [he']

theorem native_predecessor_shift {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r x z : Nat} {sources : List Nat}
    (hn : native a r = some (b, sources)) (hp : predecessor a x = some z) :
    predecessor b (shiftAfter r sources.length x) = some (shiftAfter r sources.length z) := by
  have hz := predecessor_lt valid hp
  by_cases hx : r < x
  · simp only [shiftAfter, hx, ↓reduceIte, predecessor]
    rw [native_suffix_rowAt hn hx]
    obtain ⟨row, hr, he⟩ := Option.bind_eq_some_iff.mp hp
    simp only [hr, Option.map_some, Option.bind_some, shifted_row_p, he, Option.map_some]
    rfl
  · have hsz : shiftAfter r sources.length z = z := by simp [shiftAfter, show ¬ r < z by omega]
    rw [hsz]
    simp only [shiftAfter, hx, ↓reduceIte]
    by_cases he : x = r
    · subst x; exact native_owner_predecessor valid hn hp
    · simpa only [predecessor, native_prefix_rowAt hn (by omega : x < r)] using hp

/-- Every old predecessor chain transports along the native insertion. -/
theorem native_trace_shift {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r s y : Nat} {sources xs : List Nat}
    (hn : native a r = some (b, sources)) (ht : Trace a s y xs) :
    Trace b (shiftAfter r sources.length s) (shiftAfter r sources.length y)
      (xs.map (shiftAfter r sources.length)) := by
  exact trace_map _ (shiftAfter_strict r sources.length) ht
    (fun _ _ _ hp => native_predecessor_shift valid hn hp)

/-- Marked traces of later old rows move with their rows and columns. -/
theorem native_suffix_markTrace {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r owner y : Nat} {sources xs : List Nat}
    (hn : native a r = some (b, sources)) (ht : MarkTrace a owner y xs)
    (ho : r < owner) :
    MarkTrace b (owner + sources.length) (shiftAfter r sources.length y)
      (xs.map (shiftAfter r sources.length)) := by
  obtain ⟨row, k, s, hr, hm, hk, hy, hs, ht⟩ := ht
  refine ⟨row.shiftAfter r sources.length, k, shiftAfter r sources.length s,
    ?_, ?_, hk, ?_, ?_, native_trace_shift valid hn ht⟩
  · rw [native_suffix_rowAt hn ho, hr]; rfl
  · exact List.mem_map.mpr ⟨y, hm, rfl⟩
  · simp only [Row.shiftAfter, List.getElem?_map, hy, Option.map_some]
  · simp only [Row.shiftAfter, List.getElem?_map, hs, Option.map_some]

end FullMarkedBLP


