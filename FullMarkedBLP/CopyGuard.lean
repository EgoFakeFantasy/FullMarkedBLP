import FullMarkedBLP.CopyMarks
import FullMarkedBLP.MarkTrace

namespace FullMarkedBLP

theorem copyMarkAllowed_cases {a : Pattern} {r y idx step : Nat} {core : List Nat}
    (h : copyMarkAllowed a r y core idx step = true) :
    ∃ last minimum p xs terminal,
      a.getLast? = some last ∧ last.core.head? = some minimum ∧ last.p = some p ∧
      computeMarkTrace a r y = some xs ∧ fromRight xs 2 = some terminal ∧
      (p ≤ terminal ∨ (terminal < p ∧ ∃ low, xs.find? (· < p) = some low ∧
        (low < minimum ∨ (minimum ≤ low ∧ ∃ k shifted,
          last.core.findIdx? (· == low) = some k ∧ last.core[k + last.step]? = some shifted ∧
          shifted ∈ last.marks ∧ copyPositionGuard core step idx minimum = true)))) := by
  unfold copyMarkAllowed at h
  have hh : (do
      let last ← a.getLast?
      let minimum ← last.core.head?
      let p ← last.p
      let trace ← computeMarkTrace a r y
      let penultimate ← fromRight trace 2
      if p ≤ penultimate then pure true else do
        let low ← trace.find? (· < p)
        if low < minimum then pure true else do
          let k ← last.core.findIdx? (· == low)
          let shifted ← last.core[k + last.step]?
          pure (last.marks.contains shifted && copyPositionGuard core step idx minimum)) = some true := by
    cases he : (do
      let last ← a.getLast?
      let minimum ← last.core.head?
      let p ← last.p
      let trace ← computeMarkTrace a r y
      let penultimate ← fromRight trace 2
      if p ≤ penultimate then pure true else do
        let low ← trace.find? (· < p)
        if low < minimum then pure true else do
          let k ← last.core.findIdx? (· == low)
          let shifted ← last.core[k + last.step]?
          pure (last.marks.contains shifted && copyPositionGuard core step idx minimum)) with
    | none => simp only [he, Option.getD_none, Bool.false_eq_true] at h
    | some v => have hv : v = true := by simpa only [he, Option.getD_some] using h
                exact congrArg some hv
  obtain ⟨last, hl, hh⟩ := Option.bind_eq_some_iff.mp hh
  obtain ⟨minimum, hm, hh⟩ := Option.bind_eq_some_iff.mp hh
  obtain ⟨p, hp, hh⟩ := Option.bind_eq_some_iff.mp hh
  obtain ⟨xs, hx, hh⟩ := Option.bind_eq_some_iff.mp hh
  obtain ⟨terminal, ht, hh⟩ := Option.bind_eq_some_iff.mp hh
  refine ⟨last, minimum, p, xs, terminal, hl, hm, hp, hx, ht, ?_⟩
  split at hh
  next hg => exact Or.inl hg
  next hg =>
    obtain ⟨low, hlo, hh⟩ := Option.bind_eq_some_iff.mp hh
    refine Or.inr ⟨by omega, low, hlo, ?_⟩
    split at hh
    next hmin => exact Or.inl hmin
    next hmin =>
      obtain ⟨k, hk, hh⟩ := Option.bind_eq_some_iff.mp hh
      obtain ⟨shifted, hs, hh⟩ := Option.bind_eq_some_iff.mp hh
      have hb := Bool.and_eq_true_iff.mp (Option.some.inj hh)
      exact Or.inr ⟨by omega, k, shifted, hk, hs, by simpa using hb.1, hb.2⟩

end FullMarkedBLP

