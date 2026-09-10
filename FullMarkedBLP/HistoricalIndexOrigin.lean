import FullMarkedBLP.ScanIndexOrigin
import FullMarkedBLP.ScanFrozenHistoricalCertificates

namespace FullMarkedBLP

/-- An old index image cannot lie strictly inside an inserted record block. -/
theorem historical_image_not_inside_record {phi : Nat → Nat} (mono : StrictMono phi)
    {j i owner size : Nat} (left : phi i = owner)
    (right : phi (i + 1) = owner + size + 1)
    (lo : owner ≤ phi j) (hi : phi j ≤ owner + size) : phi j = owner := by
  by_cases before : j ≤ i
  · have bound := mono.monotone before
    omega
  · have bound := mono.monotone (show i + 1 ≤ j by omega)
    omega

/-- Old-index images below the cursor either have their own record or an empty birth. -/
theorem scanReach_historical_image_origin {initial a : Pattern} {rec : Records} {r j : Nat}
    (reach : ScanReach initial a rec r) {phi : Nat → Nat} (mono : StrictMono phi)
    (alignment : ∀ owner sources, (owner, sources) ∈ rec →
      ∃ i, phi i = owner ∧ phi (i + 1) = owner + sources.length + 1)
    (positive : 0 < phi j) (passed : phi j < r) :
    (∃ sources, (phi j, sources) ∈ rec) ∨
    (∃ before after history, ScanReach initial before history (phi j) ∧
      native (completeFrozenMarks before history (phi j)) (phi j) = some (after, []) ∧
      rowAt a (phi j) = rowAt after (phi j)) := by
  rcases scanReach_processed_index_origin reach positive passed with block | empty
  · obtain ⟨owner, sources, member, lo, hi⟩ := block
    obtain ⟨i, left, right⟩ := alignment owner sources member
    have eq := historical_image_not_inside_record mono left right lo hi
    exact Or.inl ⟨sources, by simpa only [eq] using member⟩
  · exact Or.inr empty

end FullMarkedBLP
