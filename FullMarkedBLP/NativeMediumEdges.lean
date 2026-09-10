import FullMarkedBLP.NativeAllCritical

namespace FullMarkedBLP

theorem nativeLower_medium_full {row lower : Row} {owner : Nat}
    (hv : row.CoreValid owner) (ho : 0 < owner)
    (hl : nativeLower row owner true = some lower) : lower.full (owner - 1) = row.core := by
  obtain ⟨front, hf⟩ := List.getLast?_eq_some_iff.mp hv.2.2.1
  have hn : row.core.Nodup := hv.1.imp (fun h => Nat.ne_of_lt h)
  rw [hf, List.nodup_append] at hn
  have hnot : owner ∉ front := by
    intro hm
    exact hn.2.2 owner hm owner (by simp) rfl
  have he : row.core.erase owner ++ [owner] = row.core := by
    rw [hf, List.erase_append_right [owner] hnot]
    simp
  have hout : lower = ⟨row.core.erase owner, row.step, row.marks.erase (owner - 1)⟩ :=
    (Option.some.inj hl).symm
  rw [hout]
  change row.core.erase owner ++ [owner - 1 + 1] = row.core
  simpa only [Nat.sub_add_cancel (show 1 ≤ owner by omega)] using he

/-- Medium descent only removes the old implicit endpoint from the full row;
all remaining literal step edges retain their indices and the same action. -/
theorem nativeLower_medium_realizes_edges {alpha : Type u} {row lower : Row} {owner : Nat}
    (action : alpha → alpha) (theta : Nat → alpha)
    (hv : row.CoreValid owner) (ho : 0 < owner)
    (hl : nativeLower row owner true = some lower)
    (hedges : row.RealizesEdges action theta owner) :
    lower.RealizesEdges action theta (owner - 1) := by
  intro k x y hx hy
  rw [nativeLower_medium_full hv ho hl] at hx hy
  have hs := nativeLower_step hl
  simp only [↓reduceIte] at hs
  rw [hs] at hy
  exact hedges k x y (full_entry_of_core hx) (full_entry_of_core hy)

end FullMarkedBLP
