import FullMarkedBLP.PacketAllEndpoints

namespace FullMarkedBLP

/-- The actual scan fuel suffices when each reached completed pattern has valid cores. -/
theorem scanFuel_total_of_history_valid {initial : Pattern}
    (historyValid : ∀ before history owner, ScanReach initial before history owner →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    (fuel : Nat) {a : Pattern} {rec : Records} {r : Nat}
    (reach : ScanReach initial a rec r) (hbudget : a.length + 1 - r ≤ fuel) :
    ∃ result, scanFuel fuel a rec r = some result := by
  induction fuel generalizing a rec r with
  | zero =>
    have hdone : a.length < r := by omega
    exact ⟨a, by simp [scanFuel, hdone]⟩
  | succ fuel ih =>
    by_cases hdone : a.length < r
    · exact ⟨a, by simp [scanFuel, hdone]⟩
    · have hpositive := (scanReach_records_before reach).1
      have hlen := completeFrozenMarks_length a rec r
      obtain ⟨row, hr⟩ := rowAt_exists (a := completeFrozenMarks a rec r) hpositive (by omega)
      obtain ⟨b, sources, hn⟩ := native_total (historyValid a rec r reach) hr
      have hb : r ≤ a.length := by omega
      have hremaining := scan_remaining_decreases hb hn
      have reach' := ScanReach.next reach hb hn
      obtain ⟨result, hresult⟩ := ih reach' (by omega)
      refine ⟨result, ?_⟩
      simp only [scanFuel, hdone, ↓reduceIte]
      rw [hn]
      exact hresult

theorem fullScan_total_of_history_valid {a : Pattern}
    (historyValid : ∀ before history owner, ScanReach a before history owner →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i) :
    ∃ b, fullScan a = some b := by
  exact scanFuel_total_of_history_valid historyValid a.length ScanReach.start (by omega)

theorem fullScan_total_sat_of_history_valid {a : Pattern}
    (historyValid : ∀ before history owner, ScanReach a before history owner →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i) :
    ∃ b, fullScan a = some b ∧ Sat b := by
  obtain ⟨b, hb⟩ := fullScan_total_of_history_valid historyValid
  exact ⟨b, hb, fullScan_sat_of_history_valid historyValid hb⟩

end FullMarkedBLP
