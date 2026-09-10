import FullMarkedBLP.CopyRankRealization

namespace FullMarkedBLP

/-- Append one auxiliary owner, retaining every column of the old pattern. -/
noncomputable def auxiliaryColumnValues {lambda : Ordinal.{u}}
    (theta : Nat → OrdinalDomain lambda) (aux : RankElementaryEmbedding lambda) (n i : Nat) :
    OrdinalDomain lambda :=
  if i ≤ n + 1 then theta i else rankOrdinalAction aux (theta (n + 1))

noncomputable def auxiliaryEmbeddingValues {lambda : Ordinal.{u}}
    (embedding : Nat → RankElementaryEmbedding lambda) (aux : RankElementaryEmbedding lambda)
    (n i : Nat) : RankElementaryEmbedding lambda :=
  if i ≤ n then embedding i else aux

/-- A genuine auxiliary embedding with the prescribed critical point and
first edge realizes the literal appended three-point row. Its second edge
defines the new terminal column. Old natural-cutoff certificates are retained. -/
theorem rankRowRealization_auxiliary_append {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) {anchor : Nat} (ha : anchor ≤ a.length)
    (aux : RankElementaryEmbedding lambda) (critical : RankCriticalPoint aux (theta anchor))
    (edge : rankOrdinalAction aux (theta anchor) = theta (a.length + 1)) :
    RankRowRealization (a ++ [⟨[anchor, a.length + 1], 1, []⟩])
      (auxiliaryColumnValues theta aux a.length) (auxiliaryEmbeddingValues embedding aux a.length) := by
  let extended := a ++ [⟨[anchor, a.length + 1], 1, []⟩]
  have hpre : a <+: extended := List.prefix_append _ _
  have cols : ∀ i, i ≤ a.length + 1 → auxiliaryColumnValues theta aux a.length i = theta i :=
    fun i hi => if_pos hi
  have owners : ∀ i, i ≤ a.length → auxiliaryEmbeddingValues embedding aux a.length i = embedding i :=
    fun i hi => if_pos hi
  have lastOwner : auxiliaryEmbeddingValues embedding aux a.length (a.length + 1) = aux :=
    if_neg (by omega)
  have terminal : auxiliaryColumnValues theta aux a.length (a.length + 2) =
      rankOrdinalAction aux (theta (a.length + 1)) := if_neg (by omega)
  have terminalLt : theta (a.length + 1) < rankOrdinalAction aux (theta (a.length + 1)) := by
    have hh := rankOrdinalAction_strictMono aux (h.increasing anchor (a.length + 1) (by omega) le_rfl)
    rwa [edge] at hh
  have oldRow : ∀ r row, r ≤ a.length → rowAt extended r = some row → rowAt a r = some row :=
    fun r row hr hb => (prefix_rowAt hpre hr).symm.trans hb
  have newRow : ∀ r row, ¬r ≤ a.length → rowAt extended r = some row →
      r = a.length + 1 ∧ row = ⟨[anchor, a.length + 1], 1, []⟩ := by
    intro r row hn hr
    have hb := rowAt_bounds hr
    have heq : r = a.length + 1 := by
      simp only [extended, List.length_append, List.length_singleton] at hb
      omega
    refine ⟨heq, ?_⟩
    subst r
    simpa [extended, rowAt, List.getElem?_append_right (Nat.le_refl a.length)] using hr.symm
  refine ⟨auxiliary_append_coreValid h.valid ha, auxiliary_append_properMarks h.proper, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij hj
    have hj' : j ≤ a.length + 2 := by simpa using hj
    by_cases before : j ≤ a.length + 1
    · rw [cols i (by omega), cols j before]
      exact h.increasing i j hij before
    · have heq : j = a.length + 2 := by omega
      subst j
      rw [terminal, cols i (by omega)]
      by_cases same : i = a.length + 1
      · simpa [same] using terminalLt
      · exact (h.increasing i (a.length + 1) (by omega) le_rfl).trans terminalLt
  · intro i hi
    by_cases before : i ≤ a.length + 1
    · rw [cols i before]
      exact h.cardinals i before
    · rw [auxiliaryColumnValues, if_neg before]
      exact (rankOrdinalAction_cardinal_iff hl aux _).mpr (h.cardinals _ le_rfl)
  · intro r row hr
    by_cases before : r ≤ a.length
    · have hold := oldRow r row before hr
      intro i x y hx hy
      have bx := full_entry_le_endpoint (h.valid r row hold) hx
      have by' := full_entry_le_endpoint (h.valid r row hold) hy
      rw [owners r before, cols x (by omega), cols y (by omega)]
      exact h.edges r row hold i x y hx hy
    · obtain ⟨rfl, rfl⟩ := newRow r row before hr
      intro i x y hx hy
      rw [lastOwner]
      rcases i with _ | i
      · simp [Row.full] at hx hy
        subst x; subst y
        rw [cols anchor (by omega), cols (a.length + 1) le_rfl]
        exact edge
      · rcases i with _ | i
        · simp [Row.full] at hx hy
          subst x; subst y
          rw [cols (a.length + 1) le_rfl, terminal]
        · simp [Row.full] at hy
  · intro r row minimum hr hm
    by_cases before : r ≤ a.length
    · have hold := oldRow r row before hr
      have hb := core_entry_le_owner (h.valid r row hold)
        (List.mem_of_getElem? (show row.core[0]? = some minimum by
          simpa only [List.head?_eq_getElem?] using hm))
      rw [owners r before, cols minimum (by omega)]
      exact h.critical r row minimum hold hm
    · obtain ⟨rfl, rfl⟩ := newRow r row before hr
      have same : minimum = anchor := by simpa using hm.symm
      rw [same, lastOwner, cols anchor (by omega)]
      exact critical
  · intro r row y hr hy
    by_cases before : r ≤ a.length
    · have hold := oldRow r row before hr
      obtain ⟨k, s, xs, delta, hk, hky, hks, ht, hd, hw⟩ := h.marked r row y hold hy
      have hyr := (h.proper r row hold).2 y hy
      have bounded : ∀ v ∈ xs.dropLast, v ≤ a.length := by
        intro v hv
        have hb := trace_member_le_head h.valid ht (List.mem_of_mem_dropLast hv)
        omega
      have factors : ∀ v ∈ xs.dropLast,
          auxiliaryEmbeddingValues embedding aux a.length (id v) = embedding v :=
        fun v hv => owners v (bounded v hv)
      have sameCutoff := naturalCutoff_reindex_eq
        (fun i => rankOrdinalAction (embedding i))
        (fun i => rankOrdinalAction (auxiliaryEmbeddingValues embedding aux a.length i))
        theta (auxiliaryColumnValues theta aux a.length) id xs.dropLast
        (fun v hv => congrArg rankOrdinalAction (factors v hv))
        (fun v hv => cols (v + 1) (by have := bounded v hv; omega))
      refine ⟨k, s, xs, delta, hk, hky, hks, ?_, ?_, ?_⟩
      · exact trace_prefix h.valid ht (show y < a.length + 1 by omega)
          (fun i hi => (prefix_rowAt hpre (by omega)).symm)
      · simpa only [List.map_id] using sameCutoff.trans hd
      · rw [owners r before]
        intro x z hx hz
        have words := evalWord_reindex
          (fun i => (embedding i : RankDomain lambda → RankDomain lambda))
          (fun i => (auxiliaryEmbeddingValues embedding aux a.length i : RankDomain lambda → RankDomain lambda))
          id xs.dropLast (fun v hv => by dsimp only; rw [factors v hv]) z
        simp only [List.map_id] at words
        rw [words]
        exact hw x z hx hz
    · obtain ⟨_, rfl⟩ := newRow r row before hr
      simp at hy

/-- The actual assignments after appending the auxiliary row and short copying. -/
noncomputable def auxiliaryStepColumnValues {lambda : Ordinal.{u}}
    (theta : Nat → OrdinalDomain lambda) (aux : RankElementaryEmbedding lambda)
    (n anchor : Nat) : Nat → OrdinalDomain lambda :=
  shortCopyColumnValues (auxiliaryColumnValues theta aux n) aux (n + 1) anchor

noncomputable def auxiliaryStepEmbeddingValues {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) (embedding : Nat → RankElementaryEmbedding lambda)
    (aux : RankElementaryEmbedding lambda) (n anchor : Nat) : Nat → RankElementaryEmbedding lambda :=
  shortCopyEmbeddingValues hl (auxiliaryEmbeddingValues embedding aux n) (n + 1) anchor

/-- Literal auxiliary expansion preserves all row/mark data and Sat. It retains
every old column, advances the terminal by the actual auxiliary action, and
has last owner given by application to the previous last owner. -/
theorem rankMarkedRealization_auxiliaryStep {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {a b : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankMarkedRealization a theta embedding) {anchor : Nat} (ha : anchor ≤ a.length)
    (aux : RankElementaryEmbedding lambda) (critical : RankCriticalPoint aux (theta anchor))
    (edge : rankOrdinalAction aux (theta anchor) = theta (a.length + 1))
    (step : auxiliaryStep anchor a = some b) :
    RankMarkedRealization b (auxiliaryStepColumnValues theta aux a.length anchor)
      (auxiliaryStepEmbeddingValues hl embedding aux a.length anchor) ∧
    (∀ i, i ≤ a.length + 1 → auxiliaryStepColumnValues theta aux a.length anchor i = theta i) ∧
    auxiliaryStepColumnValues theta aux a.length anchor (b.length + 1) =
      rankOrdinalAction aux (theta (a.length + 1)) ∧
    auxiliaryStepEmbeddingValues hl embedding aux a.length anchor b.length =
      rankApply hl aux (embedding a.length) := by
  let row : Row := ⟨[anchor, a.length + 1], 1, []⟩
  let extended := a ++ [row]
  have hext := rankRowRealization_auxiliary_append hl (rankMarkedRealization_toRows h) ha aux critical edge
  have hlen : extended.length = a.length + 1 := by simp [extended]
  have lastGet : extended.getLast? = some row := by simp [extended]
  have lastAt : rowAt extended extended.length = some row := by
    simp [rowAt, extended]
  have hp : row.p = some anchor := by simp [row, Row.p, fromRight]
  have he : row.e = some (a.length + 1) := by simp [row, Row.e, fromRight]
  have copy : shortCopy extended = some b := step
  have outer : auxiliaryEmbeddingValues embedding aux a.length extended.length = aux := by
    rw [hlen, auxiliaryEmbeddingValues, if_neg (by omega)]
  have realization := rankRowRealization_shortCopy hl hext copy lastAt hp he
  change RankRowRealization b
    (shortCopyColumnValues (auxiliaryColumnValues theta aux a.length)
      (auxiliaryEmbeddingValues embedding aux a.length extended.length) extended.length anchor)
    (shortCopyEmbeddingValues hl (auxiliaryEmbeddingValues embedding aux a.length) extended.length anchor) at realization
  rw [outer, hlen] at realization
  have length := shortCopy_length copy lastGet hp he
  rw [hlen] at length
  have length' : b.length = a.length + (a.length + 1 - anchor) := by omega
  refine ⟨rankRowRealization_with_sat realization
    (auxiliaryStep_preserves_sat h.valid h.sat ha step), ?_, ?_, ?_⟩
  · intro i hi
    have same := shortCopyColumnValues_prefix hext lastAt hp (show i ≤ extended.length by omega)
    change shortCopyColumnValues (auxiliaryColumnValues theta aux a.length)
      (auxiliaryEmbeddingValues embedding aux a.length extended.length) extended.length anchor i = _ at same
    rw [outer, hlen] at same
    exact same.trans (if_pos hi)
  · have index : b.length + 1 - (a.length + 1 - anchor) = a.length + 1 := by omega
    simp only [auxiliaryStepColumnValues, shortCopyColumnValues, if_neg (by omega : ¬b.length + 1 < a.length + 1),
      index, auxiliaryColumnValues, if_pos (Nat.le_refl (a.length + 1))]
  · have index : b.length - (a.length + 1 - anchor) = a.length := by omega
    simp only [auxiliaryStepEmbeddingValues, shortCopyEmbeddingValues,
      if_neg (by omega : ¬b.length < a.length + 1), index, auxiliaryEmbeddingValues,
      if_neg (by omega : ¬a.length + 1 ≤ a.length), if_pos (Nat.le_refl a.length)]

theorem rankMarkedRealization_auxiliaryStep_total {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankMarkedRealization a theta embedding) {anchor : Nat}
    (positive : 0 < anchor) (ha : anchor ≤ a.length) (size : 2 ≤ a.length)
    (aux : RankElementaryEmbedding lambda) (critical : RankCriticalPoint aux (theta anchor))
    (edge : rankOrdinalAction aux (theta anchor) = theta (a.length + 1)) :
    ∃ b, auxiliaryStep anchor a = some b ∧
      RankMarkedRealization b (auxiliaryStepColumnValues theta aux a.length anchor)
        (auxiliaryStepEmbeddingValues hl embedding aux a.length anchor) := by
  obtain ⟨b, step⟩ := auxiliaryStep_total h.valid positive ha size
  exact ⟨b, step, (rankMarkedRealization_auxiliaryStep hl h ha aux critical edge step).1⟩

end FullMarkedBLP

