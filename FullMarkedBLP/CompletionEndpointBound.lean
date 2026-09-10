import FullMarkedBLP.CompletionHighColumns

namespace FullMarkedBLP

/-- A sorted row's penultimate column is determined by its upper core region. -/
theorem row_b_eq_of_high_core_iff {row out : Row} {r v w : Nat}
    (hv : row.CoreValid r) (ho : out.CoreValid r)
    (hb : row.b = some v) (hw : out.b = some w)
    (high : ∀ x, v ≤ x → (x ∈ out.core ↔ x ∈ row.core)) : w = v := by
  have vm : v ∈ row.core := by
    unfold Row.b fromRight at hb
    split at hb
    · exact List.mem_of_getElem? hb
    · simp at hb
  have wm : w ∈ out.core := by
    unfold Row.b fromRight at hw
    split at hw
    · exact List.mem_of_getElem? hw
    · simp at hw
  have vl : v < r := fromRight_lt_last hv.1 hv.2.2.1 (by decide : 1 < 2) hb
  have wl : w < r := fromRight_lt_last ho.1 ho.2.2.1 (by decide : 1 < 2) hw
  have lower : v ≤ w := core_entry_le_b ho hw ((high v (le_refl v)).mpr vm) vl
  have upper : w ≤ v := core_entry_le_b hv hb ((high w lower).mp wm) wl
  omega

/-- Completion below the old penultimate column preserves that column exactly. -/
theorem completionEvent_b_eq_of_mark_lt_b {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    {rec : Records} {r y v w : Nat}
    (event : CompletionEventGeometry a rec r y theta embedding)
    {row out : Row} (hr : rowAt a r = some row)
    (hout : rowAt (completeMark a rec r y) r = some out)
    (ho : out.CoreValid r) (hb : row.b = some v) (hw : out.b = some w)
    (hy : y < v) : w = v := by
  have vm : v ∈ row.core := by
    unfold Row.b fromRight at hb
    split at hb
    · exact List.mem_of_getElem? hb
    · simp at hb
  exact row_b_eq_of_high_core_iff (event.1.valid r row hr) ho hb hw
    (fun x hx => completionEvent_high_core_iff event hr vm hy hx hout)

/-- A frozen prefix preserves B when all its marks precede the entrance B. -/
theorem frozen_fold_b_eq_of_marks_lt_b {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    {rec : Records} {r v w : Nat} (processed : List Nat)
    (earlier : ∀ y ∈ processed, y < v)
    (events : ∀ done mark suffix, processed = done ++ mark :: suffix →
      CompletionEventGeometry
        (done.foldl (fun current y => completeMark current rec r y) a) rec r mark theta embedding)
    {row out : Row} (hr : rowAt a r = some row)
    (hout : rowAt (processed.foldl (fun current y => completeMark current rec r y) a) r = some out)
    (hv : row.CoreValid r) (ho : out.CoreValid r)
    (hb : row.b = some v) (hw : out.b = some w) : w = v := by
  have vm : v ∈ row.core := by
    unfold Row.b fromRight at hb
    split at hb
    · exact List.mem_of_getElem? hb
    · simp at hb
  exact row_b_eq_of_high_core_iff hv ho hb hw
    (fun x hx => frozen_fold_high_core_iff processed earlier events hr vm hx hout)
end FullMarkedBLP

