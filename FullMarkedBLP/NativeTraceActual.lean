import FullMarkedBLP.NativePActual

namespace FullMarkedBLP

/-- The old owner's predecessor is retained at the bottom of its native block. -/
theorem native_owner_predecessor {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r p : Nat} {sources : List Nat}
    (hn : native a r = some (b, sources))
    (hp : predecessor a r = some p) : predecessor b r = some p := by
  obtain ⟨row, hr, hn⟩ := Option.bind_eq_some_iff.mp hn
  obtain ⟨ss, hs, hn⟩ := Option.bind_eq_some_iff.mp hn
  obtain ⟨block, hb, hn⟩ := Option.bind_eq_some_iff.mp hn
  change some (_, ss) = some (b, sources) at hn
  cases Option.some.inj hn
  have hrb := rowAt_bounds hr
  have hpre : (a.take (r - 1)).length = r - 1 := by simp; omega
  have hrowp : row.p = some p := by simpa [predecessor, hr] using hp
  have hbottom := nativeBlock_bottom_p valid hr hrowp hs hb
  have hlen := nativeBlock_length hb
  have hlookup : rowAt (a.take (r - 1) ++ block ++
      (a.drop r).map (Row.shiftAfter r sources.length)) r = block.head? := by
    simp only [rowAt, show r ≠ 0 by omega, ↓reduceIte, List.append_assoc]
    rw [List.getElem?_append_right (by omega : (a.take (r - 1)).length ≤ r - 1)]
    simp only [hpre, Nat.sub_self]
    rw [List.getElem?_append_left (by omega : 0 < block.length)]
    exact List.head?_eq_getElem?.symm
  simpa only [predecessor, hlookup] using hbottom

/-- Old traces reaching the native owner remain literal traces in the output. -/
theorem native_trace_through_owner {a b : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {r s y : Nat} {sources xs : List Nat}
    (hn : native a r = some (b, sources)) (ht : Trace a s y xs)
    (hy : y ≤ r) : Trace b s y xs := by
  induction ht with
  | stop => exact Trace.stop
  | @next y z tail hlt he ht ih =>
    have hz := predecessor_lt valid he
    have he' : predecessor b y = some z := by
      by_cases hy' : y < r
      · simpa only [predecessor, native_prefix_rowAt hn hy'] using he
      · have heq : y = r := by omega
        subst y
        exact native_owner_predecessor valid hn he
    exact Trace.next hlt he' (ih (by omega))

end FullMarkedBLP

