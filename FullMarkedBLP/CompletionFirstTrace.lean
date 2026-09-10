import FullMarkedBLP.FirstParallelTrace
import FullMarkedBLP.RecordedWordDecomposition

namespace FullMarkedBLP

/-- Successful completion supplies the word decomposition and terminal record itself. -/
theorem completionRecord_first_parallel_trace {initial a : Pattern} {rec : Records}
    {r y : Nat} {sources : List Nat} (reach : ScanReach initial a rec r)
    (valid : ∀ i row, rowAt a i = some row → row.CoreValid i)
    (entrances : ∀ before history owner, ScanReach initial before history owner → owner < r →
      ∀ i row, rowAt (completeFrozenMarks before history owner) i = some row → row.CoreValid i)
    {row : Row} (hr : rowAt a r = some row) (hm : y ∈ row.marks)
    (hc : completionRecord a rec r y = some sources)
    (records : ∀ xs, computeMarkTrace a r y = some xs →
      ∀ factor ∈ xs.dropLast, ∃ ss, (factor, ss) ∈ rec) :
    ∃ xs x, computeMarkTrace a r y = some xs ∧ sources.getLast? = some x ∧
      Trace a x (y + 1) (xs.dropLast.map (fun i => i + 1) ++ [x]) := by
  obtain ⟨xs, terminal, computed, terminalAt, recorded, nonempty, guard⟩ := completionRecord_iff.mp hc
  obtain ⟨rw, k, s, _, _, _, _, _, trace⟩ := computeMarkTrace_sound hr hm computed
  obtain ⟨front, last, word⟩ := fromRight_two_decomposition terminalAt
  have head := trace_head trace
  have factors : ∃ tail, xs.dropLast = y :: tail := by
    cases front with
    | nil =>
      have eq : terminal = y := by simpa [word] using head
      exact ⟨[], by simp [word, eq]⟩
    | cons z rest =>
      have eq : z = y := by simpa [word] using head
      refine ⟨rest ++ [terminal], ?_⟩
      rw [word, eq]
      have reassoc : y :: rest ++ [terminal, last] = (y :: (rest ++ [terminal])) ++ [last] := by simp
      rw [reassoc]
      exact List.dropLast_concat
  obtain ⟨tail, factors⟩ := factors
  have lastFactor : (y :: tail).getLast? = some terminal := by
    rw [← factors, word]
    simp
  have length : 0 < sources.length := List.length_pos_iff.mpr nonempty
  obtain ⟨x, hx⟩ := fromRight_exists (xs := sources) (k := 1) (by decide) (by omega)
  have lastSource : sources.getLast? = some x := by
    simpa [fromRight, show 1 ≤ sources.length by omega, List.getLast?_eq_getElem?] using hx
  have member : (terminal, sources) ∈ rec := recordAt_mem recorded
  exact ⟨xs, x, computed, lastSource,
    currentPlusOne_recorded_first_trace reach valid entrances trace guard factors lastFactor
      (records xs computed) member lastSource⟩

end FullMarkedBLP


