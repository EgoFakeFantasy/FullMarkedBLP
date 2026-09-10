import FullMarkedBLP.RankApplicationCritical
import FullMarkedBLP.RankMarkedRealization
import FullMarkedBLP.CopyIndex

namespace FullMarkedBLP

/-- Columns for a short copy: the old prefix followed by images of the
source interval under the removed last owner. -/
noncomputable def shortCopyColumnValues {lambda : Ordinal.{u}}
    (theta : Nat → OrdinalDomain lambda) (outer : RankElementaryEmbedding lambda) (n p i : Nat) :
    OrdinalDomain lambda :=
  if i < n then theta i else rankOrdinalAction outer (theta (i - (n - p)))

noncomputable def shortCopyEmbeddingValues {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (embedding : Nat → RankElementaryEmbedding lambda) (n p i : Nat) : RankElementaryEmbedding lambda :=
  if i < n then embedding i else rankApply hl (embedding n) (embedding (i - (n - p)))

theorem shortCopyColumnValues_high {lambda : Ordinal.{u}}
    (theta : Nat → OrdinalDomain lambda) (outer : RankElementaryEmbedding lambda)
    {n p x : Nat} (hp : p ≤ n) (hx : p ≤ x) :
    shortCopyColumnValues theta outer n p (x + (n - p)) = rankOrdinalAction outer (theta x) := by
  rw [shortCopyColumnValues, if_neg (by omega)]
  congr 2
  omega

theorem shortCopyEmbeddingValues_high {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (embedding : Nat → RankElementaryEmbedding lambda) {n p x : Nat} (hp : p ≤ n) (hx : p ≤ x) :
    shortCopyEmbeddingValues hl embedding n p (x + (n - p)) = rankApply hl (embedding n) (embedding x) := by
  rw [shortCopyEmbeddingValues, if_neg (by omega)]
  congr 2
  omega

/-- The boundary column at n also keeps its old value, by the last row's p edge. -/
theorem shortCopyColumnValues_prefix {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) {last : Row} {p i : Nat}
    (lastAt : rowAt a a.length = some last) (hp : last.p = some p) (hi : i ≤ a.length) :
    shortCopyColumnValues theta (embedding a.length) a.length p i = theta i := by
  by_cases before : i < a.length
  · simp only [shortCopyColumnValues, before, if_true]
  · have same : i = a.length := by omega
    subst i
    have valid := h.valid a.length last lastAt
    have bound := fromRight_le_last valid.1 valid.2.2.1 (by omega : 0 < last.step + 1) hp
    have index : a.length - (a.length - p) = p := by omega
    rw [shortCopyColumnValues, if_neg (Nat.lt_irrefl _), index]
    exact realizesEdges_p valid (h.edges a.length last lastAt) hp

/-- Every successful branch of the literal partial copy map agrees with
the last owner's ordinal action under the actual copied column assignment. -/
theorem copyEntry_semantic_image {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) {last : Row} {p x target : Nat}
    (lastAt : rowAt a a.length = some last) (hp : last.p = some p)
    (mapped : copyEntry a.length last x = some target) :
    shortCopyColumnValues theta (embedding a.length) a.length p target = rankOrdinalAction (embedding a.length) (theta x) := by
  have valid := h.valid a.length last lastAt
  have pBound := fromRight_le_last valid.1 valid.2.2.1 (by omega : 0 < last.step + 1) hp
  obtain ⟨minimum, p', e, hmin, hp', _, _, _, cases⟩ := copyEntry_cases mapped
  have same := Option.some.inj (hp'.symm.trans hp)
  subst p'
  rcases cases with ⟨low, targetEq⟩ | ⟨_, high, targetEq⟩ | ⟨_, middle, k, sourceAt, targetAt⟩
  · subst target
    have minAt : last.core[0]? = some minimum := by simpa only [List.head?_eq_getElem?] using hmin
    have minBound := core_entry_le_owner valid (List.mem_of_getElem? minAt)
    rw [shortCopyColumnValues, if_pos (by omega)]
    exact ((h.critical a.length last minimum lastAt hmin).2 (theta x)
      (h.increasing x minimum low (by omega))).symm
  · subst target
    exact shortCopyColumnValues_high theta (embedding a.length) pBound high
  · have targetBound := copy_middle_below_owner valid hp middle sourceAt targetAt
    rw [shortCopyColumnValues, if_pos targetBound]
    exact (h.edges a.length last lastAt k x target (full_entry_of_core sourceAt) (full_entry_of_core targetAt)).symm

end FullMarkedBLP
