import FullMarkedBLP.MStarShortKey

namespace FullMarkedBLP

/-- The manuscript's two-level lexicographic comparison, on exactly the
literal states generated from `start` by `Step`. -/
def GeneratedKeyLT (a b : GeneratedPattern) : Prop := shortKey a.val < shortKey b.val

theorem rankI2_reachable_shortKey_le (i2 : RankI2.{u}) {a b : Pattern}
    (generated : Generated a) (path : Reachable a b) : shortKey b ≤ shortKey a := by
  induction path with
  | refl => exact le_rfl
  | tail path step ih =>
    exact (rankI2_generated_step_shortKey_lt i2 (reachable_generated generated path) step).le.trans ih

theorem rankI2_reachable_shortKey_lt_of_ne (i2 : RankI2.{u}) {a b : Pattern}
    (generated : Generated a) (path : Reachable a b) (different : a ≠ b) :
    shortKey b < shortKey a := by
  rcases path.cases_head with same | ⟨next, step, rest⟩
  · exact False.elim (different same)
  · exact (rankI2_reachable_shortKey_le i2 (Generated.child generated step) rest).trans_lt
      (rankI2_generated_step_shortKey_lt i2 generated step)

/-- Comparison and reachability coincide without a prior key-injectivity
assumption. Reachability comparability was proved using expansion induction. -/
theorem rankI2_shortKey_le_iff_reachable (i2 : RankI2.{u}) {a b : Pattern}
    (first : Generated a) (second : Generated b) :
    shortKey b ≤ shortKey a ↔ Reachable a b := by
  constructor
  · intro smaller
    rcases rankI2_generated_reachable_comparable i2 first second with path | path
    · exact path
    · by_cases same : a = b
      · subst b; exact .refl
      · have strict := rankI2_reachable_shortKey_lt_of_ne i2 second path (Ne.symm same)
        exact False.elim (not_lt_of_ge smaller strict)
  · exact rankI2_reachable_shortKey_le i2 first

theorem rankI2_shortKey_eq_iff (i2 : RankI2.{u}) {a b : Pattern}
    (first : Generated a) (second : Generated b) : shortKey a = shortKey b ↔ a = b := by
  constructor
  · intro equal
    by_contra different
    have path := (rankI2_shortKey_le_iff_reachable i2 first second).mp (le_of_eq equal.symm)
    have strict := rankI2_reachable_shortKey_lt_of_ne i2 first path different
    rw [equal] at strict
    exact lt_irrefl _ strict
  · exact congrArg shortKey

theorem rankI2_generated_key_injective (i2 : RankI2.{u}) :
    Function.Injective (fun a : GeneratedPattern => shortKey a.val) := by
  intro a b equal
  exact Subtype.ext ((rankI2_shortKey_eq_iff i2 a.property b.property).mp equal)

theorem rankI2_shortKey_lt_iff_reachable_ne (i2 : RankI2.{u}) {a b : Pattern}
    (first : Generated a) (second : Generated b) :
    shortKey b < shortKey a ↔ Reachable a b ∧ a ≠ b := by
  constructor
  · intro strict
    refine ⟨(rankI2_shortKey_le_iff_reachable i2 first second).mp strict.le, ?_⟩
    intro same
    subst b
    exact lt_irrefl _ strict
  · rintro ⟨path, different⟩
    exact rankI2_reachable_shortKey_lt_of_ne i2 first path different

theorem rankI2_generatedKeyLT_wellFounded (i2 : RankI2.{u}) : WellFounded GeneratedKeyLT := by
  apply (rankI2_generatedStep_wellFounded i2).transGen.mono
  intro child parent smaller
  obtain ⟨path, different⟩ :=
    (rankI2_shortKey_lt_iff_reachable_ne i2 parent.property child.property).mp smaller
  have lifted : Relation.ReflTransGen GeneratedStep parent child :=
    reachable_lift_generated parent.property path
  have nonempty : Relation.TransGen GeneratedStep parent child := by
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp lifted with same | steps
    · exact False.elim (different (congrArg Subtype.val same.symm))
    · exact steps
  exact nonempty.swap

/-- Manuscript Theorem 5.1: the specified short-key comparison is a well
order and determines the entire literal marked pattern on the generated
domain. The only hypothesis is the standard rank formulation of I2. -/
theorem rankI2_shortKey_wellOrder (i2 : RankI2.{u}) :
    IsWellOrder GeneratedPattern GeneratedKeyLT ∧
      Function.Injective (fun a : GeneratedPattern => shortKey a.val) := by
  have injective := rankI2_generated_key_injective i2
  refine ⟨?_, injective⟩
  exact { wf := rankI2_generatedKeyLT_wellFounded i2
          trichotomous := fun a b hab hba =>
            injective (le_antisymm (not_lt.mp hba) (not_lt.mp hab)) }

/-- The complete expansion and comparison conclusions for the unchanged
ordinary full-marked BLP operations and the exact standard generated domain. -/
theorem rankI2_full_marked_blp_natural_cutoff_wellorder (i2 : RankI2.{u}) :
    WellFounded (fun child parent : GeneratedPattern => Step parent.val child.val) ∧
    IsWellOrder GeneratedPattern GeneratedKeyLT ∧
    Function.Injective (fun a : GeneratedPattern => shortKey a.val) ∧
    (∀ a b : GeneratedPattern, shortKey b.val ≤ shortKey a.val ↔ Reachable a.val b.val) := by
  exact ⟨rankI2_generatedStep_wellFounded i2, (rankI2_shortKey_wellOrder i2).1,
    rankI2_generated_key_injective i2,
    fun a b => rankI2_shortKey_le_iff_reachable i2 a.property b.property⟩

end FullMarkedBLP
