import FullMarkedBLP.ScanPriorEndpointTransport

namespace FullMarkedBLP

/-- A single origin map aligns semantic assignments, the unscanned tail and
all recorded endpoints and unrecorded-row e values. Endpoint transport is an explicit prior-step obligation. -/
theorem scanRankReach_endpoint_alignment {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r : Nat}
    (h : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding) :
    ∃ (phi : Nat → Nat) (original : Nat),
      StrictMono phi ∧ phi 0 = 0 ∧ 1 ≤ original ∧ original ≤ initial.length + 1 ∧
      initial.length + r = a.length + original ∧
      (∀ i, theta (phi i) = initialTheta i ∧ embedding (phi i) = initialEmbedding i) ∧
      (∀ k, phi (original + k) = r + k) ∧
      (ScanPriorGeometry initial initialTheta initialEmbedding r →
        ∀ x z, predecessor initial x = some z → predecessor a (phi x) = some (phi z)) ∧
      (ScanPriorEndpointTransport initial initialTheta initialEmbedding r →
        ∀ x e, (rowAt initial x).bind Row.e = some e →
          (∀ ss, (phi x, ss) ∉ rec) → (rowAt a (phi x)).bind Row.e = some (phi e)) ∧
      ∀ terminal sources, (terminal, sources) ∈ rec →
        ∃ i, 1 ≤ i ∧ i < original ∧ phi i = terminal ∧ phi (i + 1) = terminal + sources.length + 1 := by
  induction h with
  | start =>
    exact ⟨id, 1, fun _ _ hij => hij, rfl, by omega, by omega, rfl,
      fun _ => ⟨rfl, rfl⟩, fun _ => rfl, fun _ _ _ hp => hp, (by intro _ x e he _; exact he), by intro terminal sources hm; simp at hm⟩
  | @next before after history owner sources oldTheta oldEmbedding reach hb hn ih =>
    obtain ⟨phi, original, hmono, hzero, hp, hmax, hlen, holds, tail, predecessors, endpoints, records⟩ := ih
    have hnew := native_length hn
    rw [completeFrozenMarks_length] at hnew
    refine ⟨fun i => shiftAfter owner sources.length (phi i), original + 1,
      fun _ _ hij => shiftAfter_strict _ _ (hmono hij), ?_, by omega, by omega, by omega,
      ?_, ?_, ?_, ?_, ?_⟩
    · simp [hzero, shiftAfter]
    · intro i
      rw [nativeColumnValues_preserves, nativeEmbeddingValues_old]
      exact holds i
    · intro k
      dsimp only
      rw [Nat.add_assoc, tail (1 + k)]
      unfold shiftAfter
      rw [if_pos (by omega)]
      omega
    · intro geometry x z hp
      have earlier := predecessors (scanPriorGeometry_mono geometry (by omega)) x z hp
      obtain ⟨valid, fixed⟩ := geometry before history owner oldTheta oldEmbedding reach (by omega)
      apply native_predecessor_shift valid hn
      rw [fixed]
      exact earlier
    · intro transport x e he missing
      have oldMissing : ∀ ss, (phi x, ss) ∉ history := by
        intro ss mem
        have beforeOwner := scanReach_record_targets_before
          (scanEmbeddingReach_forget (scanRankReach_embeddings reach)) mem
        have fixed : shiftAfter owner sources.length (phi x) = phi x := by
          simp [shiftAfter, show ¬ owner < phi x by omega]
        apply missing ss
        change (shiftAfter owner sources.length (phi x), ss) ∈ _
        rw [fixed]
        by_cases empty : sources = []
        · simpa only [empty, List.isEmpty_nil, if_true] using mem
        · simp only [List.isEmpty_iff, empty, if_false]
          exact List.mem_cons_of_mem _ mem
      have oldEndpoint := endpoints (scanPriorEndpointTransport_mono transport (by omega)) x e he oldMissing
      have unexpanded : phi x ≠ owner ∨ sources = [] := by
        by_cases eq : phi x = owner
        · right
          by_cases empty : sources = []
          · exact empty
          · have impossible := missing sources
            exfalso
            apply impossible
            simp [eq, shiftAfter, empty]
        · exact Or.inl eq
      exact transport before after history owner sources oldTheta oldEmbedding reach
        (by omega) hn (phi x) (phi e) oldEndpoint unexpanded
    · intro terminal ss hm
      have keep : (terminal, ss) ∈ history →
          ∃ i, 1 ≤ i ∧ i < original + 1 ∧ shiftAfter owner sources.length (phi i) = terminal ∧
            shiftAfter owner sources.length (phi (i + 1)) = terminal + ss.length + 1 := by
        intro hold
        obtain ⟨i, hi, hib, he, hnext⟩ := records terminal ss hold
        have ht := scanReach_record_targets_before
          (scanEmbeddingReach_forget (scanRankReach_embeddings reach)) hold
        refine ⟨i, hi, by omega, ?_, ?_⟩
        · rw [he]
          simp [shiftAfter, show ¬owner < terminal by omega]
        · rw [hnext]
          simp [shiftAfter, show ¬owner < terminal + ss.length + 1 by omega]
      by_cases hs : sources = []
      · simp only [hs, List.isEmpty_nil, if_true] at hm
        exact keep hm
      · simp only [List.isEmpty_iff, hs, if_false] at hm
        rcases List.mem_cons.mp hm with he | hold
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
          refine ⟨original, hp, by omega, ?_, ?_⟩
          · have ht : phi original = terminal := by simpa using tail 0
            simp [ht, shiftAfter]
          · dsimp only
            rw [tail 1]
            simp [shiftAfter, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        · exact keep hold

end FullMarkedBLP






