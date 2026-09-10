import FullMarkedBLP.NativeMediumEdges

namespace FullMarkedBLP

/-- In short descent the lower full row is the old core with precisely its
source endpoint removed; the old owner becomes the new implicit endpoint. -/
theorem nativeLower_short_full {row lower : Row} {owner e : Nat}
    (hv : row.CoreValid owner) (ho : 0 < owner) (hs : 1 < row.step)
    (he : row.e = some e) (hl : nativeLower row owner false = some lower) :
    lower.full (owner - 1) = row.core.erase e := by
  have heo := fromRight_lt_last hv.1 hv.2.2.1 hs he
  obtain ⟨front, hf⟩ := List.getLast?_eq_some_iff.mp hv.2.2.1
  have hnodup : row.core.Nodup := hv.1.imp (fun h => Nat.ne_of_lt h)
  rw [hf, List.nodup_append] at hnodup
  have hnot : owner ∉ front := by
    intro hm
    exact hnodup.2.2 owner hm owner (by simp) rfl
  have hei : row.core[row.core.length - row.step]? = some e := by
    simpa [Row.e, fromRight, hv.2.2.2.1, (Row.step_lt_length hv.2.2.2).le] using he
  have hem : e ∈ row.core := List.mem_of_getElem? hei
  have hef : e ∈ front := by
    rw [hf, List.mem_append, List.mem_singleton] at hem
    exact hem.resolve_right (by omega)
  have hout : lower = ⟨(row.core.erase owner).erase e, row.step - 1,
      row.marks.erase (owner - 1)⟩ := by
    unfold nativeLower at hl
    simp only [Bool.false_eq_true, ↓reduceIte, he] at hl
    exact (Option.some.inj hl).symm
  rw [hout]
  change (row.core.erase owner).erase e ++ [owner - 1 + 1] = row.core.erase e
  rw [Nat.sub_add_cancel (show 1 ≤ owner by omega), hf,
    List.erase_append_right [owner] hnot, List.erase_append_left [owner] hef]
  simp

end FullMarkedBLP

