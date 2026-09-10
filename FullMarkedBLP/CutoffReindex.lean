import FullMarkedBLP.RankPacketTransfer

namespace FullMarkedBLP

/-- Reindexing unchanged factors and lowering their successor columns can only
lower the natural cutoff. Hypotheses concern the factors of this word only. -/
theorem naturalCutoff_reindex_le {alpha : Type u} [Preorder alpha]
    (oldAction newAction : Nat → alpha → alpha) (oldTheta newTheta : Nat → alpha)
    (phi : Nat → Nat) (word : List Nat)
    (mono : ∀ v, Monotone (oldAction v))
    (factors : ∀ v ∈ word, newAction (phi v) = oldAction v)
    (successors : ∀ v ∈ word, newTheta (phi v + 1) ≤ oldTheta (v + 1))
    {oldDelta newDelta : alpha}
    (ho : naturalCutoff oldAction oldTheta word = some oldDelta)
    (hn : naturalCutoff newAction newTheta (word.map phi) = some newDelta) :
    newDelta ≤ oldDelta := by
  induction word generalizing oldDelta newDelta with
  | nil => simp [naturalCutoff] at ho
  | cons v tail ih =>
    cases tail with
    | nil =>
      have heo : oldTheta (v + 1) = oldDelta := Option.some.inj ho
      have hen : newTheta (phi v + 1) = newDelta := Option.some.inj hn
      rw [← heo, ← hen]
      exact successors v (by simp)
    | cons w rest =>
      obtain ⟨od, hod⟩ := naturalCutoff_defined oldAction oldTheta (word := w :: rest) (by simp)
      obtain ⟨nd, hnd⟩ := naturalCutoff_defined newAction newTheta
        (word := (w :: rest).map phi) (by simp)
      have hle : nd ≤ od := ih
        (fun i hi => factors i (List.mem_cons_of_mem v hi))
        (fun i hi => successors i (List.mem_cons_of_mem v hi)) hod hnd
      have heo : oldAction v od = oldDelta := by
        simpa only [naturalCutoff, hod, Option.map_some, Option.some.injEq] using ho
      simp only [List.map_cons] at hnd
      have hen : newAction (phi v) nd = newDelta := by
        simpa only [Option.some.injEq] using
          (show (some (newAction (phi v) nd) : Option alpha) = some newDelta from by
            simpa only [List.map_cons, naturalCutoff, hnd, Option.map_some] using hn)
      rw [← heo, ← hen, factors v (by simp)]
      exact mono v hle

end FullMarkedBLP


