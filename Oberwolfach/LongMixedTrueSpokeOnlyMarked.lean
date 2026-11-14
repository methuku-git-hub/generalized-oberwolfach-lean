module

public import Oberwolfach.LongRawMatchingHubPacking

@[expose] public section
/-! In the mixed matching, a true-marked spoke can be covered only by a
marked wheel; ordinary wheel resources use false-spoke labels. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_mixed_true_spoke_only_marked
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (c:Σi,longRawSeedFamilies (U:=U) π d m ℓ i) (v:Fin n) (w:U)
    (h:Sum.inr (true,v,w)∈mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ) c):
    c.1=none:=by
  rcases c with ⟨i,c⟩
  cases i with
  | none => rfl
  | some i =>
    exfalso
    change Sum.inr (true,v,w)∈(orderedOrdinaryResources c).map ordinaryMarkedResourceEmbedding at h
    obtain ⟨a,ha,he⟩:=Finset.mem_map.mp h
    cases a with
    | inl e => simp [ordinaryMarkedResourceEmbedding,orderedOrdinaryResourceEmbedding] at he
    | inr a => simp [ordinaryMarkedResourceEmbedding,orderedOrdinaryResourceEmbedding] at he
end Oberwolfach
