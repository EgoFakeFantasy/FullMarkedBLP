import FullMarkedBLP.PacketEndpoint

namespace FullMarkedBLP

/-- Every guarded internal factor edge has the exact successor as its e endpoint. -/
theorem currentPlusOne_all_endpoints {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {s y : Nat} {xs : List Nat} (ht : Trace a s y xs)
    (hg : currentPlusOne a xs = true) :
    ∀ parent child, (parent, child) ∈ xs.dropLast.zip xs.dropLast.tail →
      ∃ row, rowAt a parent = some row ∧ row.p = some child ∧ row.e = some (child + 1) := by
  induction ht with
  | stop => simp
  | @next y z tail hsy hp ht ih =>
    have hguard := currentPlusOne_tail hg
    cases tail with
    | nil => exact False.elim (trace_nonempty ht rfl)
    | cons child rest =>
      cases rest with
      | nil => simp
      | cons next rest =>
        have hchild : child = z := by simpa using trace_head ht
        subst child
        intro parent child hm
        simp only [List.dropLast_cons_cons, List.tail_cons, List.zip_cons_cons, List.mem_cons] at hm
        rcases hm with heq | hm
        · obtain ⟨heq1, heq2⟩ := Prod.mk.inj heq
          subst parent; subst child
          exact currentPlusOne_head_endpoint valid (Trace.next hsy hp ht) hg
        · exact ih hguard parent child hm

/-- The scanned-prefix Sat invariant gives every eligible internal endpoint bound. -/
theorem scan_packet_all_b_bounds {initial a : Pattern} {rec : Records} {cursor : Nat}
    (historyValid : ∀ before history owner, ScanReach initial before history owner →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (reach : ScanReach initial a rec cursor)
    {s y : Nat} {xs : List Nat} (ht : Trace a s y xs)
    (hg : currentPlusOne a xs = true) (hy : y < cursor) :
    ∀ parent child, (parent, child) ∈ xs.dropLast.zip xs.dropLast.tail →
      (∀ row, rowAt a parent = some row → row.core.length ≤ 2 * row.step) →
      ∃ er v, rowAt a (child + 1) = some er ∧ er.b = some v ∧ v ≤ child := by
  intro parent child hm heligible
  obtain ⟨row, hr, hp, he⟩ := currentPlusOne_all_endpoints valid ht hg parent child hm
  have hmem : parent ∈ xs := (List.dropLast_sublist xs).subset (List.of_mem_zip hm).1
  have hparent := trace_member_le_head valid ht hmem
  obtain ⟨p, e, er, v, hp', he', her, hb, hle⟩ :=
    scanReach_sat_prefix historyValid reach parent row (by omega) hr (heligible row hr)
  have hpeq := Option.some.inj (hp'.symm.trans hp)
  have heeq := Option.some.inj (he'.symm.trans he)
  subst p; subst e
  exact ⟨er, v, her, hb, hle⟩

/-- The first successor endpoint bound requires only core validity, even for long factors. -/
theorem currentPlusOne_all_endpoint_b_bounds {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {s y : Nat} {xs : List Nat} (ht : Trace a s y xs)
    (hg : currentPlusOne a xs = true) :
    ∀ parent child, (parent, child) ∈ xs.dropLast.zip xs.dropLast.tail →
      ∃ er v, rowAt a (child + 1) = some er ∧ er.b = some v ∧ v ≤ child := by
  intro parent child hm
  obtain ⟨row, hr, _, he⟩ := currentPlusOne_all_endpoints valid ht hg parent child hm
  have hv := valid parent row hr
  have heBound := fromRight_le_last hv.1 hv.2.2.1 hv.2.2.2.1 he
  have hparent := (rowAt_bounds hr).2
  obtain ⟨er, her⟩ := rowAt_exists (a := a) (by omega : 0 < child + 1) (by omega)
  have hver := valid (child + 1) er her
  obtain ⟨v, hb⟩ := Row.b_exists hver
  have hlt := fromRight_lt_last hver.1 hver.2.2.1 (by decide : 1 < 2) hb
  exact ⟨er, v, her, hb, by omega⟩

end FullMarkedBLP


