import FullMarkedBLP.CardinalFreshChoice
import Mathlib.SetTheory.Cardinal.Arithmetic

namespace FullMarkedBLP

/-- Sequence form of the omega-Jonsson property: every equicardinal subset
realizes every color by a countable sequence of its own members. -/
def IsOmegaJonsson {X : Type u} (color : (Nat → X) → X) : Prop :=
  ∀ A : Set X, Cardinal.mk A = Cardinal.mk X →
    ∀ value : X, ∃ sequence : Nat → X, (∀ n, sequence n ∈ A) ∧ color sequence = value

/-- Kunen's direct construction in the case where the number of countable
sequences equals the size of the powerset. A fresh sequence is assigned to
every pair consisting of a large subset and a desired color. -/
theorem exists_omegaJonsson_of_countable_power (X : Type u) [Nonempty X]
    (infinite : Cardinal.aleph0 ≤ Cardinal.mk X)
    (power : Cardinal.mk X ^ Cardinal.aleph0 = 2 ^ Cardinal.mk X) :
    ∃ color : (Nat → X) → X, IsOmegaJonsson color := by
  classical
  let I := {A : Set X // Cardinal.mk A = Cardinal.mk X} × X
  let allowed : I → Set (Nat → X) := fun i => {sequence | ∀ n, sequence n ∈ i.1.val}
  have requirements : Cardinal.mk I ≤ 2 ^ Cardinal.mk X := by
    have injective : Function.Injective (fun i : I => (i.1.val, i.2)) := by
      intro i k same
      have first : i.1 = k.1 := Subtype.ext (congrArg (fun p : Set X × X => p.1) same)
      exact Prod.ext first (congrArg (fun p : Set X × X => p.2) same)
    apply (Cardinal.mk_le_of_injective injective).trans_eq
    rw [Cardinal.mk_prod, Cardinal.mk_set]
    simp only [Cardinal.lift_id]
    apply Cardinal.mul_eq_left (infinite.trans (Cardinal.cantor _).le) (Cardinal.cantor _).le
    exact ne_of_gt (Cardinal.aleph0_pos.trans_le infinite)
  have allowedCard : ∀ i, Cardinal.mk (allowed i) = 2 ^ Cardinal.mk X := by
    intro i
    have eqv : allowed i ≃ (Nat → i.1.val) := Equiv.subtypePiEquivPi
    rw [Cardinal.mk_congr eqv, Cardinal.mk_arrow]
    simp only [Cardinal.mk_nat, Cardinal.lift_aleph0, Cardinal.lift_uzero]
    rw [i.1.property, power]
  obtain ⟨selected, injective, member⟩ := exists_injective_choice_of_cardinal_bound allowed
    (fun i => requirements.trans_eq (allowedCard i).symm)
  letI : Nonempty I := ⟨⟨⟨Set.univ, by simp⟩, Classical.choice (inferInstance : Nonempty X)⟩⟩
  let color : (Nat → X) → X := fun sequence => (Function.invFun selected sequence).2
  refine ⟨color, ?_⟩
  intro A cardA value
  let index : I := ⟨⟨A, cardA⟩, value⟩
  refine ⟨selected index, member index, ?_⟩
  change (Function.invFun selected (selected index)).2 = value
  rw [Function.leftInverse_invFun injective index]

end FullMarkedBLP
