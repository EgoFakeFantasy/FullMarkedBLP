import FullMarkedBLP.CopySatPrefix

namespace FullMarkedBLP

/-- Every reachable history is empty in the inherited prefix; all recorded owners lie beyond it. -/
theorem shortCopy_scan_record_region {a copied current : Pattern} {rec : Records} {cursor : Nat}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (hs : Sat a) (hcopy : shortCopy a = some copied)
    (reach : ScanReach copied current rec cursor) :
    (cursor ≤ a.length → current = copied ∧ rec = []) ∧
      (∀ entry ∈ rec, a.length ≤ entry.1) := by
  induction reach with
  | start => exact ⟨fun _ => ⟨rfl, rfl⟩, by simp⟩
  | @next before after history owner sources previous hb hn ih =>
    by_cases howner : owner < a.length
    · obtain ⟨hbefore, hhistory⟩ := ih.1 (by omega)
      subst before; subst history
      have hpositive := (scanReach_records_before previous).1
      obtain ⟨row, hr⟩ := rowAt_exists (a := a) hpositive (by omega)
      have hnative := shortCopy_sat_prefix_native valid hs hcopy hr howner
      have hn' : native copied owner = some (after, sources) := by
        simpa only [completeFrozenMarks_empty] using hn
      obtain ⟨heq, hsrc⟩ := Prod.mk.inj (Option.some.inj (hn'.symm.trans hnative))
      subst after; subst sources
      simp
    · constructor
      · intro hbound
        omega
      · intro entry hentry
        by_cases hnil : sources = []
        · simp only [hnil, List.isEmpty_nil, ↓reduceIte] at hentry
          exact ih.2 entry hentry
        · simp only [List.isEmpty_iff, hnil, ↓reduceIte] at hentry
          rcases List.mem_cons.mp hentry with heq | hm
          · subst entry; dsimp; omega
          · exact ih.2 entry hm

theorem shortCopy_completion_terminal_region {a copied current : Pattern}
    {rec : Records} {cursor y : Nat} {sources : List Nat}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (hs : Sat a) (hcopy : shortCopy a = some copied)
    (reach : ScanReach copied current rec cursor)
    (hc : completionRecord current rec cursor y = some sources) :
    ∃ xs terminal, computeMarkTrace current cursor y = some xs ∧
      fromRight xs 2 = some terminal ∧ a.length ≤ terminal ∧ terminal < cursor := by
  obtain ⟨xs, terminal, hxs, ht, hr, _, _⟩ := completionRecord_iff.mp hc
  have hm := recordAt_mem hr
  have hlo := (shortCopy_scan_record_region valid hs hcopy reach).2 (terminal, sources) hm
  have hhi := (scanReach_records_before reach).2 (terminal, sources) hm
  exact ⟨xs, terminal, hxs, ht, hlo, hhi.2.1⟩

theorem trace_factor_ge_terminal {a : Pattern}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    {s y terminal factor : Nat} {xs : List Nat}
    (ht : Trace a s y xs) (hf : fromRight xs 2 = some terminal)
    (hm : factor ∈ xs.dropLast) : terminal ≤ factor := by
  induction ht with
  | stop => simp at hm
  | @next y z tail hsy hp ht ih =>
    have hterminal := trace_terminal_factor valid (Trace.next hsy hp ht) hf
    cases tail with
    | nil => exact False.elim (trace_nonempty ht rfl)
    | cons v rest =>
      simp only [List.dropLast_cons_cons, List.mem_cons] at hm
      rcases hm with heq | hm
      · omega
      · cases rest with
        | nil => simp at hm
        | cons w rest =>
          have hf' : fromRight (v :: w :: rest) 2 = some terminal := by
            simpa only [fromRight_cons_of_le (by simp : 2 ≤ (v :: w :: rest).length)] using hf
          exact ih hf' hm

theorem shortCopy_completion_factor_region {a copied current : Pattern}
    {rec : Records} {cursor y : Nat} {sources : List Nat} {row : Row}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (currentValid : ∀ r row, rowAt current r = some row → row.CoreValid r)
    (hs : Sat a) (hcopy : shortCopy a = some copied)
    (reach : ScanReach copied current rec cursor)
    (hrow : rowAt current cursor = some row) (hmark : y ∈ row.marks)
    (hc : completionRecord current rec cursor y = some sources) :
    ∃ xs, MarkTrace current cursor y xs ∧
      ∀ factor ∈ xs.dropLast, a.length ≤ factor := by
  obtain ⟨xs, terminal, hxs, ht, hlo, _⟩ := shortCopy_completion_terminal_region valid hs hcopy reach hc
  have hm := computeMarkTrace_sound hrow hmark hxs
  refine ⟨xs, hm, ?_⟩
  intro factor hf
  obtain ⟨old, k, s, _, _, _, _, _, htrace⟩ := hm
  have hb := trace_factor_ge_terminal currentValid htrace ht hf
  omega

end FullMarkedBLP

