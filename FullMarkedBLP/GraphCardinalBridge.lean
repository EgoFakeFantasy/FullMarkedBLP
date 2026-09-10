import FullMarkedBLP.RankBijectionConditions
import Mathlib.SetTheory.ZFC.Cardinal

namespace FullMarkedBLP

theorem zfGraph_bijective_function {x y f : ZFSet.{u}} (hf : ZFSet.IsFunc x y f)
    (ho : ∀ b ∈ y, ∃ a ∈ x, ZFSet.pair a b ∈ f)
    (hi : ∀ a ∈ x, ∀ c ∈ x, ∀ b : ZFSet.{u},
      ZFSet.pair a b ∈ f → ZFSet.pair c b ∈ f → a = c) :
    ∃ g : x → y, Function.Bijective g := by
  classical
  have ht : ∀ a : x, ∃ b : y, ZFSet.pair a.val b.val ∈ f := by
    intro a
    obtain ⟨b, hb, _⟩ := hf.2 a.val a.property
    exact ⟨⟨b, (ZFSet.pair_mem_prod.mp (hf.1 hb)).2⟩, hb⟩
  choose g hg using ht
  refine ⟨g, ?_, ?_⟩
  · intro a c he
    apply Subtype.ext
    exact hi a.val a.property c.val c.property (g a).val (hg a)
      (by rw [he]; exact hg c)
  · intro b
    obtain ⟨a, ha, hab⟩ := ho b.val b.property
    refine ⟨⟨a, ha⟩, ?_⟩
    apply Subtype.ext
    obtain ⟨v, hv, hu⟩ := hf.2 a ha
    exact (hu _ (hg ⟨a, ha⟩)).trans (hu _ hab).symm

theorem zfGraph_card_eq {x y f : ZFSet.{u}} (hf : ZFSet.IsFunc x y f)
    (ho : ∀ b ∈ y, ∃ a ∈ x, ZFSet.pair a b ∈ f)
    (hi : ∀ a ∈ x, ∀ c ∈ x, ∀ b : ZFSet.{u},
      ZFSet.pair a b ∈ f → ZFSet.pair c b ∈ f → a = c) : x.card = y.card := by
  obtain ⟨g, hg⟩ := zfGraph_bijective_function hf ho hi
  have hh := Cardinal.mk_congr (Equiv.ofBijective g hg)
  simpa only [ZFSet.cardinalMk_coe_sort, Cardinal.lift_inj] using hh

end FullMarkedBLP
