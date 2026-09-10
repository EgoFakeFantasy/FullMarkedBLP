import FullMarkedBLP.PrefixChildren
import FullMarkedBLP.AccessibleBranchChain

namespace FullMarkedBLP

abbrev Reachable (a b : Pattern) : Prop := Relation.ReflTransGen Step a b

theorem reachable_generated {a b : Pattern} (generated : Generated a) (path : Reachable a b) : Generated b := by
  induction path with
  | refl => exact generated
  | tail _ step ih => exact Generated.child ih step

theorem generated_reachable {a : Pattern} (generated : Generated a) : Reachable start a := by
  induction generated with
  | root => exact .refl
  | child _ step ih => exact ih.tail step

theorem prefix_cut_reachable {a b : Pattern} (initialSegment : b <+: a) (size : 2 ≤ b.length) : Reachable a b := by
  obtain ⟨tail, rfl⟩ := initialSegment
  induction tail using List.reverseRecOn with
  | nil => simpa only [List.append_nil] using (Relation.ReflTransGen.refl : Reachable b b)
  | append_singleton tail row ih =>
    have cutEq : cut (b ++ (tail ++ [row])) = some (b ++ tail) := by
      have positive : 2 < (b ++ (tail ++ [row])).length := by simp only [List.length_append, List.length_singleton]; omega
      rw [cut, if_pos positive, ← List.append_assoc, List.dropLast_append_cons]
      simp
    exact Relation.ReflTransGen.head (Step.cut cutEq) ih

theorem rankI2_generated_valid_sat (i2 : RankI2.{u}) {a : Pattern} (generated : Generated a) :
    (∀ r row, rowAt a r = some row → row.CoreValid r) ∧ Sat a := by
  obtain ⟨lambda, hl, theta, embedding, root⟩ := rankI2_full_root i2
  obtain ⟨newTheta, newEmbedding, realized, _, _⟩ := rankFullMarkedRealization_generated hl root generated
  exact ⟨realized.rows.valid, realized.rows.sat⟩

theorem step_parent_length {a b : Pattern} (step : Step a b) : 2 < a.length := by
  by_contra small
  have small : a.length ≤ 2 := Nat.le_of_not_gt small
  cases step with
  | cut h => simp [cut, Nat.not_lt.mpr small] at h
  | expand _ h =>
    unfold expand at h
    split at h
    next =>
      obtain ⟨last, _, rest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨anchor, _, rest⟩ := Option.bind_eq_some_iff.mp rest
      obtain ⟨initial, cutEq, _⟩ := Option.bind_eq_some_iff.mp rest
      simp [cut, Nat.not_lt.mpr small] at cutEq
    next => simp at h
  | marked h =>
    unfold mStar at h
    split at h
    next =>
      obtain ⟨copied, copy, _⟩ := Option.bind_eq_some_iff.mp h
      simp [shortCopy, small] at copy
    next => simp at h

theorem rankI2_generated_length (i2 : RankI2.{u}) {a : Pattern} (generated : Generated a) : 2 ≤ a.length := by
  cases generated with
  | root => decide
  | @child parent child gen step =>
    obtain ⟨valid, sat⟩ := rankI2_generated_valid_sat i2 gen
    have lengthBound := (step_cut_prefix valid sat step).length_le
    have size := step_parent_length step
    simp only [List.length_dropLast] at lengthBound
    omega

abbrev GeneratedPattern := {a : Pattern // Generated a}
def GeneratedStep (parent child : GeneratedPattern) : Prop := Step parent.val child.val

theorem reachable_lift_generated {a b : Pattern} (generated : Generated a) (path : Reachable a b) :
    Relation.ReflTransGen GeneratedStep ⟨a, generated⟩ ⟨b, reachable_generated generated path⟩ := by
  induction path with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail step

theorem reachable_forget_generated {a b : GeneratedPattern}
    (path : Relation.ReflTransGen GeneratedStep a b) : Reachable a.val b.val := by
  induction path with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail step

/-- Together with proved expansion well-foundedness, literal nesting of
siblings makes the whole generated domain a chain under reachability.
This argument precedes and does not assume short-key injectivity. -/
theorem rankI2_generated_reachable_comparable (i2 : RankI2.{u}) {a b : Pattern}
    (first : Generated a) (second : Generated b) : Reachable a b ∨ Reachable b a := by
  have branches : ∀ parent x y : GeneratedPattern, GeneratedStep parent x → GeneratedStep parent y →
      Relation.ReflTransGen GeneratedStep x y ∨ Relation.ReflTransGen GeneratedStep y x := by
    intro parent x y px py
    obtain ⟨valid, sat⟩ := rankI2_generated_valid_sat i2 parent.property
    rcases step_children_prefix_comparable valid sat px py with xy | yx
    · exact Or.inr (reachable_lift_generated y.property (prefix_cut_reachable xy (rankI2_generated_length i2 x.property)))
    · exact Or.inl (reachable_lift_generated x.property (prefix_cut_reachable yx (rankI2_generated_length i2 y.property)))
  have accessible : Acc (fun child parent => GeneratedStep parent child) (⟨start, Generated.root⟩ : GeneratedPattern) :=
    (rankI2_generatedStep_wellFounded i2).apply _
  have result := accessible_descendants_comparable branches accessible ⟨a, first⟩ ⟨b, second⟩
    (reachable_lift_generated Generated.root (generated_reachable first))
    (reachable_lift_generated Generated.root (generated_reachable second))
  exact result.imp reachable_forget_generated reachable_forget_generated

end FullMarkedBLP
