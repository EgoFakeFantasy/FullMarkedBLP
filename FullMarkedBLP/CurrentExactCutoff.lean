import FullMarkedBLP.CurrentSuccessorEdge

namespace FullMarkedBLP

theorem currentPlusOne_trace_cutoff {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) {s y : Nat} {xs : List Nat}
    {delta : OrdinalDomain lambda} (ht : Trace a s y xs)
    (hc : currentPlusOne a xs = true)
    (hd : naturalCutoff (fun i => rankOrdinalAction (embedding i)) theta xs.dropLast = some delta) :
    delta = theta (y + 1) := by
  induction ht generalizing delta with
  | stop => simp [naturalCutoff] at hd
  | @next y z tail hsy hp ht ih =>
    cases tail with
    | nil => exact False.elim (trace_nonempty ht rfl)
    | cons v rest =>
      have hv : v = z := by simpa using trace_head ht
      subst v
      cases rest with
      | nil => simpa [naturalCutoff] using hd.symm
      | cons w rest =>
        have hc' : currentPlusOne a (z :: w :: rest) = true := by
          simpa [currentPlusOne, List.dropLast_cons_cons] using
            (show currentPlusOne a (z :: w :: rest) = true from by
              simp [currentPlusOne, List.dropLast_cons_cons] at hc ⊢
              exact hc.2)
        obtain ⟨row, hr, hm⟩ := currentPlusOne_iff.mp hc y z (by
          simp [List.dropLast_cons_cons])
        have hrp : row.p = some z := by simpa [predecessor, hr] using hp
        obtain ⟨epsilon, he⟩ := naturalCutoff_defined (fun i => rankOrdinalAction (embedding i)) theta
          (word := (z :: w :: rest).dropLast) (by simp)
        have hi := ih hc' he
        have hedge := realized_successor_edge h hr hrp hm
        simp only [List.dropLast_cons_cons] at he
        simp only [List.dropLast_cons_cons, naturalCutoff, he, Option.map_some, Option.some.injEq] at hd
        rw [hi, hedge] at hd
        exact hd.symm

end FullMarkedBLP
