import FullMarkedBLP.ScanStepUnexpandedEndpoint

namespace FullMarkedBLP

/-- Endpoint transport obligations at strictly earlier actual scan steps. -/
def ScanPriorEndpointTransport {lambda : Ordinal.{u}} (initial : Pattern)
    (initialTheta : Nat → OrdinalDomain lambda)
    (initialEmbedding : Nat → RankElementaryEmbedding lambda) (cursor : Nat) : Prop :=
  ∀ before after history owner sources theta embedding,
    ScanRankReach initial initialTheta initialEmbedding before history owner theta embedding →
    owner < cursor → native (completeFrozenMarks before history owner) owner = some (after, sources) →
    ∀ i e, (rowAt before i).bind Row.e = some e → (i ≠ owner ∨ sources = []) →
      (rowAt after (shiftAfter owner sources.length i)).bind Row.e =
        some (shiftAfter owner sources.length e)

theorem scanPriorEndpointTransport_mono {lambda : Ordinal.{u}} {initial : Pattern}
    {initialTheta : Nat → OrdinalDomain lambda}
    {initialEmbedding : Nat → RankElementaryEmbedding lambda} {r s : Nat}
    (h : ScanPriorEndpointTransport initial initialTheta initialEmbedding r) (le : s ≤ r) :
    ScanPriorEndpointTransport initial initialTheta initialEmbedding s := by
  intro before after history owner sources theta embedding reach lt birth i e he unexpanded
  exact h before after history owner sources theta embedding reach (by omega) birth i e he unexpanded

/-- Verified prior realizations and events discharge the transport obligations. -/
theorem scanPriorEndpointTransport_of_events {lambda : Ordinal.{u}} {initial : Pattern}
    {initialTheta : Nat → OrdinalDomain lambda}
    {initialEmbedding : Nat → RankElementaryEmbedding lambda} {cursor : Nat}
    (historyValid : ∀ before history owner, ScanReach initial before history owner → owner < cursor →
      ∀ i rw, rowAt (completeFrozenMarks before history owner) i = some rw → rw.CoreValid i)
    (verified : ∀ before history owner theta embedding,
      ScanRankReach initial initialTheta initialEmbedding before history owner theta embedding → owner < cursor →
      RankRowRealization before theta embedding ∧
      ∀ row, rowAt before owner = some row → ∀ done mark suffix, row.marks = done ++ mark :: suffix →
        CompletionEventGeometry
          (done.foldl (fun current y => completeMark current history owner y) before)
          history owner mark theta embedding) :
    ScanPriorEndpointTransport initial initialTheta initialEmbedding cursor := by
  intro before after history owner sources theta embedding reach lt birth i e he unexpanded
  obtain ⟨h, events⟩ := verified before history owner theta embedding reach lt
  obtain ⟨row, hr, endpoint⟩ := Option.bind_eq_some_iff.mp he
  have plain := scanEmbeddingReach_forget (scanRankReach_embeddings reach)
  obtain ⟨completedOwner, ownerAt, _⟩ := Option.bind_eq_some_iff.mp birth
  have bounds := rowAt_bounds ownerAt
  obtain ⟨ownerRow, atOwner⟩ := rowAt_exists (a := before) bounds.1
    (by simpa only [completeFrozenMarks_length] using bounds.2)
  exact scan_step_unexpanded_endpoint
    (fun a rec r reached earlier => historyValid a rec r reached (by omega))
    plain h atOwner hr endpoint (events ownerRow atOwner) birth unexpanded
end FullMarkedBLP

