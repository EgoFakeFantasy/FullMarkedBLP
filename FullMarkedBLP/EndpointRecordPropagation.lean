import FullMarkedBLP.ScanEndpointAlignment
import FullMarkedBLP.HistoricalIndexOrigin

namespace FullMarkedBLP

/-- The first target of a nonempty inserted block is not an old index image. -/
theorem historical_image_ne_first_target {phi : Nat → Nat} (mono : StrictMono phi)
    {i owner size : Nat} (left : phi i = owner)
    (right : phi (i + 1) = owner + size + 1) (positive : 0 < size) (j : Nat) :
    phi j ≠ owner + 1 := by
  intro eq
  have same := historical_image_not_inside_record mono left right
    (j := j) (by omega) (by omega)
  omega

/-- With the coherent origin map, a +1 endpoint above a record forces an upper record. -/
theorem scanRankReach_endpoint_record_propagation {lambda : Ordinal.{u}} {initial a : Pattern}
    {initialTheta theta : Nat → OrdinalDomain lambda}
    {initialEmbedding embedding : Nat → RankElementaryEmbedding lambda} {rec : Records} {r : Nat}
    (reach : ScanRankReach initial initialTheta initialEmbedding a rec r theta embedding)
    (transport : ScanPriorEndpointTransport initial initialTheta initialEmbedding r)
    (initialValid : ∀ i row, rowAt initial i = some row → row.CoreValid i) :
    ∃ phi : Nat → Nat, StrictMono phi ∧ phi 0 = 0 ∧
      (∀ i, theta (phi i) = initialTheta i ∧ embedding (phi i) = initialEmbedding i) ∧
      (∀ lower ss, (lower, ss) ∈ rec →
        ∃ j, phi j = lower ∧ phi (j + 1) = lower + ss.length + 1) ∧
      ∀ x original current lower ss,
        rowAt initial x = some original → rowAt a (phi x) = some current →
        current.e = some (lower + 1) → (lower, ss) ∈ rec →
        ∃ upperSources, (phi x, upperSources) ∈ rec := by
  obtain ⟨phi, originalIndex, mono, zero, _, _, _, holds, _, _, endpoints, records⟩ :=
    scanRankReach_endpoint_alignment reach
  have aligned : ∀ lower ss, (lower, ss) ∈ rec →
      ∃ j, phi j = lower ∧ phi (j + 1) = lower + ss.length + 1 := by
    intro lower ss member
    obtain ⟨j, _, _, left, right⟩ := records lower ss member
    exact ⟨j, left, right⟩
  refine ⟨phi, mono, zero, holds, aligned, ?_⟩
  intro x original current lower ss atOriginal atCurrent endpoint member
  by_contra missing
  have noRecord : ∀ upperSources, (phi x, upperSources) ∉ rec := by
    intro upperSources mem
    exact missing ⟨upperSources, mem⟩
  have valid := initialValid x original atOriginal
  have room := Row.step_lt_length valid.2.2.2
  obtain ⟨e, he⟩ := fromRight_exists (xs := original.core) (k := original.step)
    valid.2.2.2.1 (by omega)
  have oldE : (rowAt initial x).bind Row.e = some e := by
    simp only [atOriginal, Option.bind_some]
    exact he
  have mapped := endpoints transport x e oldE noRecord
  have eq : phi e = lower + 1 := by
    simp only [atCurrent, Option.bind_some, endpoint, Option.some.injEq] at mapped
    exact mapped.symm
  obtain ⟨j, left, right⟩ := aligned lower ss member
  have nonempty : ss ≠ [] :=
    ((scanReach_records_before (scanEmbeddingReach_forget (scanRankReach_embeddings reach))).2
      (lower, ss) member).2.2
  exact historical_image_ne_first_target mono left right (List.length_pos_iff.mpr nonempty) e eq

end FullMarkedBLP
