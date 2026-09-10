import FullMarkedBLP.NativeProperClosure

namespace FullMarkedBLP

/-- Trace transport needs only the predecessor equations actually used. -/
theorem trace_map {a b : Pattern} {s y : Nat} {xs : List Nat} (f : Nat → Nat)
    (hf : ∀ {x y}, x < y → f x < f y)
    (h : Trace a s y xs)
    (hp : ∀ x z, x ∈ xs → predecessor a x = some z → predecessor b (f x) = some (f z)) :
    Trace b (f s) (f y) (xs.map f) := by
  induction h with
  | stop => exact Trace.stop
  | @next y z tail hlt he ht ih =>
    exact Trace.next (hf hlt) (hp y z (by simp) he)
      (ih (fun x z hx hz => hp x z (List.mem_cons_of_mem y hx) hz))

/-- A trace below an unchanged row prefix cannot be affected by later rows. -/
theorem trace_prefix {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {s y bound : Nat} {xs : List Nat} (h : Trace a s y xs) (hy : y < bound)
    (hp : ∀ i, i < bound → rowAt a i = rowAt b i) : Trace b s y xs := by
  induction h with
  | stop => exact Trace.stop
  | @next y z tail hlt he ht ih =>
    have hz := predecessor_lt valid he
    have he' : predecessor b y = some z := by
      simpa only [predecessor, ← hp y hy] using he
    exact Trace.next hlt he' (ih (by omega))

theorem native_prefix_rowAt {a b : Pattern} {r : Nat} {sources : List Nat}
    (h : native a r = some (b, sources)) {i : Nat} (hi : i < r) :
    rowAt b i = rowAt a i := by
  obtain ⟨row, hr, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ss, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨block, _, h⟩ := Option.bind_eq_some_iff.mp h
  change some (_, ss) = some (b, sources) at h
  cases Option.some.inj h
  by_cases hz : i = 0
  · subst i; simp [rowAt]
  · have hb := rowAt_bounds hr
    have hidx : i - 1 < (a.take (r - 1)).length := by simp; omega
    simp [rowAt, hz, List.append_assoc, List.getElem?_append_left hidx,
      show i - 1 < r - 1 by omega]

theorem native_prefix_trace {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r s y : Nat} {sources xs : List Nat}
    (hn : native a r = some (b, sources)) (ht : Trace a s y xs) (hy : y < r) :
    Trace b s y xs :=
  trace_prefix valid ht hy (fun _ hi => (native_prefix_rowAt hn hi).symm)

theorem native_prefix_markTrace {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (marks : ∀ r row, rowAt a r = some row → row.ProperMarks r)
    {r owner y : Nat} {sources xs : List Nat}
    (hn : native a r = some (b, sources)) (ht : MarkTrace a owner y xs) (ho : owner < r) :
    MarkTrace b owner y xs := by
  obtain ⟨row, k, s, hr, hm, hk, hy, hs, ht⟩ := ht
  have hless := ((marks owner row hr).2 y hm).1
  refine ⟨row, k, s, ?_, hm, hk, hy, hs, native_prefix_trace valid hn ht (by omega)⟩
  rw [native_prefix_rowAt hn ho]
  exact hr


theorem fromRight_map (f : Nat → Nat) (xs : List Nat) (k : Nat) :
    fromRight (xs.map f) k = (fromRight xs k).map f := by
  unfold fromRight
  simp only [List.length_map]
  split <;> simp_all

theorem shifted_row_p (row : Row) (r t : Nat) :
    (row.shiftAfter r t).p = row.p.map (shiftAfter r t) := by
  exact fromRight_map _ _ _

theorem shifted_row_e (row : Row) (r t : Nat) :
    (row.shiftAfter r t).e = row.e.map (shiftAfter r t) := by
  exact fromRight_map _ _ _

/-- Successful short-copy prefixes retain every earlier row verbatim. -/
theorem prefix_rowAt {a b : Pattern} (hp : a <+: b) {i : Nat} (hi : i ≤ a.length) :
    rowAt b i = rowAt a i := by
  obtain ⟨tail, rfl⟩ := hp
  by_cases hz : i = 0
  · subst i; simp [rowAt]
  · have hh : i - 1 < a.length := by omega
    simp [rowAt, hz, List.getElem?_append_left hh]

end FullMarkedBLP
