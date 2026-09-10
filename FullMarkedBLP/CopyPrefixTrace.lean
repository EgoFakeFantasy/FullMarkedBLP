import FullMarkedBLP.CopyProperClosure
import FullMarkedBLP.TraceTransport

namespace FullMarkedBLP

theorem shortCopy_prefix_rowAt {a b : Pattern} (h : shortCopy a = some b)
    {i : Nat} (hi : i < a.length) : rowAt b i = rowAt a i := by
  unfold shortCopy at h
  split at h
  next => simp at h
  next =>
    obtain ⟨last, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨sources, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨copied, _, h⟩ := Option.bind_eq_some_iff.mp h
    cases Option.some.inj h
    by_cases hz : i = 0
    · simp [rowAt, hz]
    · have hb : i - 1 < a.dropLast.length := by simp; omega
      simp only [rowAt, hz, ↓reduceIte, List.getElem?_append_left hb]
      simp [List.dropLast_eq_take,
        show i - 1 < a.length - 1 by omega]

theorem shortCopy_prefix_trace {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (h : shortCopy a = some b) {s y : Nat} {xs : List Nat}
    (ht : Trace a s y xs) (hy : y < a.length) : Trace b s y xs :=
  trace_prefix valid ht hy (fun _ hi => (shortCopy_prefix_rowAt h hi).symm)

theorem shortCopy_prefix_markTrace {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (marks : ∀ r row, rowAt a r = some row → row.ProperMarks r)
    (h : shortCopy a = some b) {r y : Nat} {xs : List Nat}
    (ht : MarkTrace a r y xs) (hr : r < a.length) : MarkTrace b r y xs := by
  obtain ⟨row, k, s, hrow, hm, hk, hy, hs, ht⟩ := ht
  refine ⟨row, k, s, (shortCopy_prefix_rowAt h hr).trans hrow, hm, hk, hy, hs, ?_⟩
  have hylt := (marks r row hrow).2 y hm
  exact shortCopy_prefix_trace valid h ht (by omega)

end FullMarkedBLP


