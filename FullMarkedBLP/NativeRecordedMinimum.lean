import FullMarkedBLP.NativeMinimum

namespace FullMarkedBLP

theorem native_nonempty_bottom_minimum {a b : Pattern} {owner : Nat} {sources : List Nat}
    (valid : ∀ r row, rowAt a r = some row → row.CoreValid r)
    (hn : native a owner = some (b, sources)) (hne : sources ≠ []) :
    ∃ row minimum p, rowAt b owner = some row ∧ row.core.head? = some minimum ∧
      row.p = some p ∧ minimum < p := by
  obtain ⟨old, hr, _⟩ := Option.bind_eq_some_iff.mp hn
  have hv := valid owner old hr
  have hroom := Row.step_lt_length hv.2.2.2
  obtain ⟨p, hp⟩ := fromRight_exists (xs := old.core) (k := old.step + 1) (by omega) (by omega)
  obtain ⟨e, he⟩ := fromRight_exists (xs := old.core) (k := old.step) hv.2.2.2.1 (by omega)
  have hlength : 0 < sources.length := List.length_pos_iff.mpr hne
  obtain ⟨last, hl⟩ := fromRight_exists (xs := sources) (k := 1) (by omega) (by omega)
  have hlast : sources.getLast? = some last := by
    simpa [fromRight, show 1 ≤ sources.length by omega, List.getLast?_eq_getElem?] using hl
  have hsrc := native_sources_of_success hn
  obtain ⟨row, er, v, hout, hrp, hre, _, _, _⟩ := native_bottom_sat_witness valid hr hp he hsrc hlast hn
  have hvout := native_preserves_coreValid valid hn owner row hout
  have hlo := nativeSources_below_owner valid hr hsrc last (List.mem_of_getLast? hlast)
  have hlen : 0 < row.core.length := by have := hvout.2.1; omega
  let minimum := row.core[0]'hlen
  have hm : row.core.head? = some minimum := by simp [List.head?_eq_getElem?, minimum]
  have hpbound := Row.step_lt_length hvout.2.2.2
  have hpi : row.core[row.core.length - (row.step + 1)]? = some p := by
    simpa [Row.p, fromRight, show row.step + 1 ≤ row.core.length by omega] using hrp
  have hle := core_head_le_entry hvout hm hpi
  refine ⟨row, minimum, p, hout, hm, hrp, ?_⟩
  by_contra hh
  have heq : p = minimum := by omega
  obtain ⟨hcore, hstep⟩ := row_p_minimum_shape hvout hm (by simpa [heq] using hrp)
  have heowner : row.e = some owner := by simp [Row.e, fromRight, hcore, hstep]
  have heLast := Option.some.inj (heowner.symm.trans hre)
  omega

theorem scanReach_record_minimum_lt_p {initial a : Pattern} {rec : Records} {cursor : Nat}
    (historyValid : ∀ before history owner, ScanReach initial before history owner → owner < cursor →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    (reach : ScanReach initial a rec cursor) {terminal : Nat} {sources : List Nat}
    (hm : (terminal, sources) ∈ rec) (hne : sources ≠ []) :
    ∃ row minimum p, rowAt a terminal = some row ∧ row.core.head? = some minimum ∧
      row.p = some p ∧ minimum < p := by
  revert historyValid
  induction reach with
  | start => simp at hm
  | @next before after history owner ss previous hb hn ih =>
    intro historyValid
    have preserve : (terminal, sources) ∈ history →
        ∃ row minimum p, rowAt after terminal = some row ∧ row.core.head? = some minimum ∧
          row.p = some p ∧ minimum < p := by
      intro hh
      obtain ⟨row, minimum, p, hr, hmin, hp, hlt⟩ := ih hh (fun before history oldOwner prior bound => historyValid before history oldOwner prior (by omega))
      have hbefore := scanReach_record_targets_before previous hh
      exact ⟨row, minimum, p, (scan_step_prefix_rowAt hn (by omega)).trans hr, hmin, hp, hlt⟩
    by_cases hs : ss = []
    · simp only [hs, List.isEmpty_nil, ↓reduceIte] at hm
      exact preserve hm
    · simp only [List.isEmpty_iff, hs, ↓reduceIte] at hm
      rcases List.mem_cons.mp hm with he | hh
      · obtain ⟨he1, he2⟩ := Prod.mk.inj he
        subst terminal; subst sources
        exact native_nonempty_bottom_minimum (historyValid before history owner previous (by omega)) hn hne
      · exact preserve hh

theorem terminal_factor_mem {xs : List Nat} {terminal : Nat}
    (h : fromRight xs 2 = some terminal) : terminal ∈ xs.dropLast := by
  unfold fromRight at h
  split at h
  next hb =>
    have hg : xs.dropLast[xs.length - 2]? = some terminal := by
      simpa only [List.dropLast_eq_take, List.getElem?_take, if_pos (show xs.length - 2 < xs.length - 1 by omega)] using h
    exact List.mem_of_getElem? hg
  next => simp at h

theorem realized_completion_source_above_minimum_of_records {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    {rec : Records} {r y minimum : Nat} {row : Row} {sources : List Nat}
    (recordMinimum : ∀ terminal ss, (terminal, ss) ∈ rec → ss ≠ [] →
      ∃ rw low p, rowAt a terminal = some rw ∧ rw.core.head? = some low ∧
        rw.p = some p ∧ low < p)
    (h : RankRowRealization a theta embedding)
    (hr : rowAt a r = some row) (hy : y ∈ row.marks) (hm : row.core.head? = some minimum)
    (hc : completionRecord a rec r y = some sources) :
    ∃ k s xs, row.step ≤ k ∧ row.core[k]? = some y ∧ row.core[k - row.step]? = some s ∧
      Trace a s y xs ∧ minimum < s := by
  obtain ⟨xs, hmark, hfactor⟩ := rankRealization_mark_factor_minima h hr hy hm
  obtain ⟨ys, terminal, hcompute, hterminal, hrecord, hnonempty, _⟩ := completionRecord_iff.mp hc
  have he := Option.some.inj (hcompute.symm.trans (computeMarkTrace_complete h.valid hmark))
  subst ys
  obtain ⟨old, k, s, hold, _, hk, hky, hks, ht⟩ := hmark
  have heold := Option.some.inj (hold.symm.trans hr)
  subst old
  have hpred := (trace_terminal_factor h.valid ht hterminal).1
  obtain ⟨terminalRow, tmin, p, htr, htm, htp, hlt⟩ :=
    recordMinimum terminal sources (recordAt_mem hrecord) hnonempty
  have hp : predecessor a terminal = some p := by simp [predecessor, htr, htp]
  have hps := Option.some.inj (hp.symm.trans hpred)
  have hmin := hfactor terminal (terminal_factor_mem hterminal) terminalRow tmin htr htm
  exact ⟨k, s, xs, hk, hky, hks, ht, by omega⟩

theorem realized_completion_source_above_minimum {lambda : Ordinal.{u}} {initial a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    {rec : Records} {r y minimum : Nat} {row : Row} {sources : List Nat}
    (historyValid : ∀ before history owner, ScanReach initial before history owner → owner < r →
      ∀ i rw, rowAt (completeFrozenMarks before history owner) i = some rw → rw.CoreValid i)
    (reach : ScanReach initial a rec r) (h : RankRowRealization a theta embedding)
    (hr : rowAt a r = some row) (hy : y ∈ row.marks) (hm : row.core.head? = some minimum)
    (hc : completionRecord a rec r y = some sources) :
    ∃ k s xs, row.step ≤ k ∧ row.core[k]? = some y ∧ row.core[k - row.step]? = some s ∧
      Trace a s y xs ∧ minimum < s := by
  exact realized_completion_source_above_minimum_of_records
    (fun _ _ hm hne => scanReach_record_minimum_lt_p historyValid reach hm hne) h hr hy hm hc
/-- Historical record minima survive any current-owner completion prefix. -/
theorem scanReach_record_minimum_frozen_prefix {initial a : Pattern} {rec : Records} {r : Nat}
    (historyValid : ∀ before history owner, ScanReach initial before history owner → owner < r →
      ∀ i rw, rowAt (completeFrozenMarks before history owner) i = some rw → rw.CoreValid i)
    (reach : ScanReach initial a rec r) (processed : List Nat)
    {terminal : Nat} {sources : List Nat} (hm : (terminal, sources) ∈ rec) (hne : sources ≠ []) :
    ∃ rw low p,
      rowAt (processed.foldl (fun current mark => completeMark current rec r mark) a) terminal = some rw ∧
      rw.core.head? = some low ∧ rw.p = some p ∧ low < p := by
  obtain ⟨rw, low, p, hr, hmin, hp, hlt⟩ := scanReach_record_minimum_lt_p historyValid reach hm hne
  have bound := scanReach_record_targets_before reach hm
  exact ⟨rw, low, p, (completeMarks_fold_other_row processed (by omega : terminal ≠ r)).trans hr,
    hmin, hp, hlt⟩

/-- The source-above-minimum argument applies at intermediate frozen states;
it needs their realization, but not an artificial ScanReach proof for them. -/
theorem realized_completion_source_above_minimum_frozen_prefix
    {lambda : Ordinal.{u}} {initial a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    {rec : Records} {r y minimum : Nat} {row : Row} {sources : List Nat}
    (historyValid : ∀ before history owner, ScanReach initial before history owner → owner < r →
      ∀ i rw, rowAt (completeFrozenMarks before history owner) i = some rw → rw.CoreValid i)
    (reach : ScanReach initial a rec r) (processed : List Nat)
    (h : RankRowRealization
      (processed.foldl (fun current mark => completeMark current rec r mark) a) theta embedding)
    (hr : rowAt (processed.foldl (fun current mark => completeMark current rec r mark) a) r = some row)
    (hy : y ∈ row.marks) (hm : row.core.head? = some minimum)
    (hc : completionRecord (processed.foldl (fun current mark => completeMark current rec r mark) a)
      rec r y = some sources) :
    ∃ k s xs, row.step ≤ k ∧ row.core[k]? = some y ∧ row.core[k - row.step]? = some s ∧
      Trace (processed.foldl (fun current mark => completeMark current rec r mark) a) s y xs ∧ minimum < s := by
  exact realized_completion_source_above_minimum_of_records
    (fun _ _ hm hne => scanReach_record_minimum_frozen_prefix historyValid reach processed hm hne)
    h hr hy hm hc

end FullMarkedBLP








