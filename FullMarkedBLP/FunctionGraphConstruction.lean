import FullMarkedBLP.GraphCardinalBridge

namespace FullMarkedBLP

noncomputable def zfFunctionGraph {x y : ZFSet.{u}} (g : x → y) : ZFSet.{u} :=
  ZFSet.range (fun a : x => ZFSet.pair a.val (g a).val)

theorem mem_zfFunctionGraph {x y : ZFSet.{u}} (g : x → y) (a b : ZFSet.{u}) :
    ZFSet.pair a b ∈ zfFunctionGraph g ↔ ∃ ha : a ∈ x, (g ⟨a, ha⟩).val = b := by
  simp only [zfFunctionGraph, ZFSet.mem_range, ZFSet.pair_inj]
  constructor
  · rintro ⟨⟨c, hc⟩, he, hb⟩
    change c = a at he
    subst c
    exact ⟨hc, hb⟩
  · rintro ⟨ha, hb⟩
    exact ⟨⟨a, ha⟩, rfl, hb⟩

theorem zfFunctionGraph_isFunc {x y : ZFSet.{u}} (g : x → y) :
    ZFSet.IsFunc x y (zfFunctionGraph g) := by
  constructor
  · intro p hp
    obtain ⟨a, rfl⟩ := ZFSet.mem_range.mp hp
    exact ZFSet.pair_mem_prod.mpr ⟨a.property, (g a).property⟩
  · intro a ha
    refine ⟨(g ⟨a, ha⟩).val, (mem_zfFunctionGraph g _ _).mpr ⟨ha, rfl⟩, ?_⟩
    intro b hb
    obtain ⟨ha', he⟩ := (mem_zfFunctionGraph g _ _).mp hb
    exact he.symm

theorem zfFunctionGraph_onto {x y : ZFSet.{u}} (g : x → y) (hg : Function.Surjective g) :
    ∀ b ∈ y, ∃ a ∈ x, ZFSet.pair a b ∈ zfFunctionGraph g := by
  intro b hb
  obtain ⟨a, ha⟩ := hg ⟨b, hb⟩
  exact ⟨a.val, a.property, (mem_zfFunctionGraph g _ _).mpr
    ⟨a.property, congrArg Subtype.val ha⟩⟩

theorem zfFunctionGraph_oneToOne {x y : ZFSet.{u}} (g : x → y) (hg : Function.Injective g) :
    ∀ a ∈ x, ∀ c ∈ x, ∀ b : ZFSet.{u},
      ZFSet.pair a b ∈ zfFunctionGraph g → ZFSet.pair c b ∈ zfFunctionGraph g → a = c := by
  intro a ha c hc b hab hcb
  obtain ⟨ha', hab'⟩ := (mem_zfFunctionGraph g _ _).mp hab
  obtain ⟨hc', hcb'⟩ := (mem_zfFunctionGraph g _ _).mp hcb
  exact congrArg Subtype.val (hg (Subtype.ext (hab'.trans hcb'.symm)))

end FullMarkedBLP

