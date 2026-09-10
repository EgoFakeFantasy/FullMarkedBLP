import FullMarkedBLP.FullRankRealization
import FullMarkedBLP.RankFiniteLining

namespace FullMarkedBLP

/-- Concrete witnesses for the SAME literal standard root using h = g ◦ g.
This gives an alternative existence proof; it makes no assertion about the
manuscript's specific g_(11) word or its additional critical-point estimates. -/
noncomputable def compositionRootEmbedding {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) (g : RankElementaryEmbedding lambda) :
    Nat → RankElementaryEmbedding lambda
  | 0 => g
  | 1 => g
  | 2 => g
  | 3 => g.comp g
  | 4 => g.comp g
  | _ + 5 => rankApply hl (g.comp g) (g.comp g)

/-- The finite standard-root row/mark certificate follows from any genuine
critical point. All column cardinality, edges, critical points, Sat and the
single exact natural-cutoff mark are constructed. Linedness is separate. -/
theorem rankMarkedRealization_composition_root {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {g : RankElementaryEmbedding lambda}
    {critical : OrdinalDomain lambda} (cp : RankCriticalPoint g critical) :
    RankMarkedRealization start (rankCriticalSequence g critical) (compositionRootEmbedding hl g) := by
  have doubleCp : RankCriticalPoint (g.comp g) critical := by
    simpa using rankCriticalPoint_comp cp cp
  have appliedCp : RankCriticalPoint (rankApply hl (g.comp g) (g.comp g))
      (rankCriticalSequence g critical 2) := by
    have h := rankApply_criticalPoint hl (g.comp g) doubleCp
    change RankCriticalPoint (rankApply hl (g.comp g) (g.comp g))
      (rankOrdinalAction (g.comp g) (rankCriticalSequence g critical 0)) at h
    rwa [rankCriticalSequence_double] at h
  refine ⟨fun _ _ hr => start_core_valid hr, fun _ _ hr => start_proper_marks hr,
    start_sat, fun _ _ hij _ => rankCriticalSequence_strictMono cp hij,
    fun i _ => rankCriticalSequence_cardinal hl cp i, ?_, ?_, ?_⟩
  · intro r row hr
    rcases start_row_index hr with hr' | hr' | hr' | hr' | hr' <;>
      subst r <;> simp [rowAt, start, zero] at hr <;> subst row
    all_goals
      intro i x y hx hy
      have bound := (List.getElem?_eq_some_iff.mp hy).1
      simp only [Row.full, List.length_append, List.length_cons, List.length_nil] at bound
      have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases cases with hi | hi | hi | hi <;> subst i <;>
        simp [Row.full] at hx hy <;> subst x <;> subst y
    all_goals
      simp only [compositionRootEmbedding]
      first
      | rfl
      | exact rankCriticalSequence_double g critical 0
      | exact rankCriticalSequence_double g critical 1
      | exact rankCriticalSequence_double g critical 2
      | exact rankCriticalSequence_double g critical 3
      | exact rankCriticalSequence_applied_double hl g critical 0
      | exact rankCriticalSequence_applied_double hl g critical 1
      | exact rankCriticalSequence_applied_double hl g critical 2
  · intro r row minimum hr hm
    rcases start_row_index hr with hr' | hr' | hr' | hr' | hr' <;>
      subst r <;> simp [rowAt, start, zero] at hr <;> subst row <;>
      simp at hm <;> subst minimum
    · exact cp
    · exact cp
    · exact doubleCp
    · exact doubleCp
    · exact appliedCp
  · intro r row y hr hy
    rcases start_row_index hr with hr' | hr' | hr' | hr' | hr' <;>
      subst r <;> simp [rowAt, start, zero] at hr <;> subst row <;> simp at hy
    subst y
    refine ⟨3, 1, [3, 1], rankCriticalSequence g critical 4,
      by decide, by decide, by decide, Trace.next (by decide) (by decide) Trace.stop, rfl, ?_⟩
    intro x z hx hz
    rfl

/-- Any complete first-triple family extends the concrete finite root
certificate to the manuscript's full semantic certificate. -/
theorem rankFullMarkedRealization_composition_root {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {g : RankElementaryEmbedding lambda}
    {critical : OrdinalDomain lambda} (cp : RankCriticalPoint g critical)
    (lined : RankAllFiniteLined critical (rankCriticalSequence g critical 1) (rankCriticalSequence g critical 2)) :
    RankFullMarkedRealization start (rankCriticalSequence g critical) (compositionRootEmbedding hl g) :=
  ⟨rankMarkedRealization_composition_root hl cp, lined⟩

/-- Concrete finite-endpoint embeddings suffice for a full standard root.
The I2 construction of this embedding family remains explicitly unproved;
no root-realization or linedness conclusion is assumed in its place. -/
theorem rankFullMarkedRealization_root_of_endpoint_embeddings {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {critical left right : OrdinalDomain lambda}
    (family : ∀ k, 0 < k → ∃ j : RankElementaryEmbedding lambda,
      RankCriticalPoint j critical ∧ rankOrdinalAction j critical = left ∧
        rankCriticalSequence j critical (k + 1) = right) :
    ∃ (theta : Nat → OrdinalDomain lambda) (embedding : Nat → RankElementaryEmbedding lambda),
      RankFullMarkedRealization start theta embedding ∧
        theta 0 = critical ∧ theta 1 = left ∧ theta 2 = right := by
  obtain ⟨g, cp, first, last⟩ := family 1 (by omega)
  have lined := rankAllFiniteLined_of_endpoint_embeddings hl family
  have first' : rankCriticalSequence g critical 1 = left := first
  have last' : rankCriticalSequence g critical 2 = right := last
  rw [← first', ← last'] at lined
  exact ⟨_, _, rankFullMarkedRealization_composition_root hl cp lined, rfl, first', last'⟩

end FullMarkedBLP
