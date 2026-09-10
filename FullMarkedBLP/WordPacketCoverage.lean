import FullMarkedBLP.NativeHistoricalEdgeTransfer

namespace FullMarkedBLP

theorem rankWord_strictMono {lambda : Ordinal.{u}}
    (embedding : Nat → RankElementaryEmbedding lambda) (word : List Nat) :
    StrictMono (evalWord (fun i => rankOrdinalAction (embedding i)) word) := by
  intro x y hxy
  simpa only [rankWordEmbedding_ordinalAction] using
    rankOrdinalAction_strictMono (rankWordEmbedding embedding word) hxy

theorem terminal_packet_below_natural_cutoff {lambda : Ordinal.{u}}
    (embedding : Nat → RankElementaryEmbedding lambda) (theta : Nat → OrdinalDomain lambda)
    (front : List Nat) (terminal : Nat) {target delta : OrdinalDomain lambda}
    (ht : target < theta (terminal + 1))
    (hd : naturalCutoff (fun i => rankOrdinalAction (embedding i)) theta (front ++ [terminal]) = some delta) :
    evalWord (fun i => rankOrdinalAction (embedding i)) front target < delta := by
  rw [naturalCutoff_snoc] at hd
  have he := Option.some.inj hd
  rw [← he]
  exact rankWord_strictMono embedding front ht

theorem native_packet_word_target_covered {lambda : Ordinal.{u}} {a : Pattern}
    {theta : Nat → OrdinalDomain lambda} {embedding : Nat → RankElementaryEmbedding lambda}
    (h : RankRowRealization a theta embedding) {r p e : Nat} {row : Row} {sources : List Nat}
    (hr : rowAt a r = some row) (hp : row.p = some p) (he : row.e = some e)
    (hs : nativeSources a r = some sources) (front : List Nat) {delta : OrdinalDomain lambda}
    (hd : naturalCutoff (fun i => rankOrdinalAction (embedding i)) theta (front ++ [r]) = some delta)
    (k : Nat) :
    evalWord (fun i => rankOrdinalAction (embedding i)) front
      (nativeFreshValues theta (embedding r) r sources k) < delta :=
  terminal_packet_below_natural_cutoff embedding theta front r
    (rankRealization_native_fresh_upper h hr hp he hs k) hd

end FullMarkedBLP

