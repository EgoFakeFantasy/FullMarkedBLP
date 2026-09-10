import FullMarkedBLP.RankCertificateReindex

namespace FullMarkedBLP

theorem naturalCutoff_reindex_eq {alpha : Type u}
    (oldAction newAction : Nat → alpha → alpha) (oldTheta newTheta : Nat → alpha)
    (phi : Nat → Nat) (word : List Nat)
    (factors : ∀ v ∈ word, newAction (phi v) = oldAction v)
    (successors : ∀ v ∈ word, newTheta (phi v + 1) = oldTheta (v + 1)) :
    naturalCutoff newAction newTheta (word.map phi) = naturalCutoff oldAction oldTheta word := by
  induction word with
  | nil => rfl
  | cons v tail ih =>
    cases tail with
    | nil => simpa only [List.map_cons, List.map_nil, naturalCutoff] using
        congrArg some (successors v (by simp))
    | cons w tail =>
      simp only [List.map_cons, naturalCutoff]
      have rest := ih (fun i hi => factors i (List.mem_cons_of_mem v hi))
        (fun i hi => successors i (List.mem_cons_of_mem v hi))
      simp only [List.map_cons] at rest
      rw [rest, factors v (by simp)]

end FullMarkedBLP
