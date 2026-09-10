import Mathlib.SetTheory.ZFC.Ordinal
import Mathlib.SetTheory.ZFC.VonNeumann
import FullMarkedBLP.TraceWordSemantics

namespace FullMarkedBLP

/-- The manuscript's weak relation on actual ZFC sets and rank cutoffs. -/
def zfcCutoffAgreement (delta : Ordinal.{u}) (f g : ZFSet.{u} → ZFSet.{u}) : Prop :=
  cutoffAgreement (· ∈ ·) (fun (d : Ordinal.{u}) (x : ZFSet.{u}) => x.rank < d) delta f g

theorem zfcCutoffAgreement_iff_vonNeumann {delta : Ordinal.{u}} {f g : ZFSet.{u} → ZFSet.{u}} :
    zfcCutoffAgreement delta f g ↔
      ∀ x ∈ ZFSet.vonNeumann delta, ∀ z ∈ ZFSet.vonNeumann delta,
        (x ∈ f z ↔ x ∈ g z) := by
  simp only [zfcCutoffAgreement, cutoffAgreement, ZFSet.mem_vonNeumann]
  constructor
  · intro h x hx z hz
    exact h x z hx hz
  · intro h x z hx hz
    exact h x hx z hz

theorem zfcCutoffAgreement_reads_edge {delta target : Ordinal.{u}}
    {f g : ZFSet.{u} → ZFSet.{u}} {z : ZFSet.{u}}
    (h : zfcCutoffAgreement delta f g) (hz : z.rank < delta)
    (hf : f z = target.toZFSet) (hg : ZFSet.IsOrdinal (g z))
    (ht : target < delta) : g z = target.toZFSet := by
  exact cutoffAgreement_reads_edge (· ∈ ·) (fun (d : Ordinal.{u}) (x : ZFSet.{u}) => x.rank < d) Ordinal.toZFSet (· < ·)
    (fun x => lt_irrefl x) (fun hxy hyz => lt_trans hxy hyz)
    (fun x y => by rcases lt_trichotomy x y with h | h | h; exact Or.inr (Or.inl h); exact Or.inl h; exact Or.inr (Or.inr h))
    (fun x y => Ordinal.toZFSet_mem_toZFSet_iff)
    (fun d x hx => by simpa only [Ordinal.rank_toZFSet] using hx) h hz hf
    ⟨(g z).rank, hg.toZFSet_rank_eq.symm⟩ ht

/-- The actual rank-initial domain on which the intended embeddings act. -/
abbrev RankDomain (lambda : Ordinal.{u}) := {x : ZFSet.{u} // x.rank < lambda}

noncomputable def extendRankMap {lambda : Ordinal.{u}}
    (f : RankDomain lambda → RankDomain lambda) (x : ZFSet.{u}) : ZFSet.{u} := by
  classical
  exact if hx : x.rank < lambda then (f ⟨x, hx⟩).val else x

theorem extendRankMap_inside {lambda : Ordinal.{u}}
    (f : RankDomain lambda → RankDomain lambda) (x : RankDomain lambda) :
    extendRankMap f x.val = (f x).val := by
  simp [extendRankMap, x.property]

def rankCutoffAgreement {lambda : Ordinal.{u}} (delta : Ordinal.{u})
    (f g : RankDomain lambda → RankDomain lambda) : Prop :=
  ∀ x z : RankDomain lambda, x.val.rank < delta → z.val.rank < delta →
    (x.val ∈ (f z).val ↔ x.val ∈ (g z).val)

theorem rankCutoffAgreement_iff_extension {lambda delta : Ordinal.{u}}
    {f g : RankDomain lambda → RankDomain lambda} (hd : delta ≤ lambda) :
    rankCutoffAgreement delta f g ↔ zfcCutoffAgreement delta (extendRankMap f) (extendRankMap g) := by
  constructor
  · intro h x z hx hz
    let x' : RankDomain lambda := ⟨x, lt_of_lt_of_le hx hd⟩
    let z' : RankDomain lambda := ⟨z, lt_of_lt_of_le hz hd⟩
    have hh := h x' z' hx hz
    simpa [extendRankMap, x', z', lt_of_lt_of_le hz hd] using hh
  · intro h x z hx hz
    have hh := h x.val z.val hx hz
    simpa only [extendRankMap_inside] using hh

end FullMarkedBLP


