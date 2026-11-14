module

public import Oberwolfach.LongRawHubContext
public import Oberwolfach.MixedSeedResourceSizes

@[expose] public section
/-! The actual mixed long-preparation candidate types have bounded nonempty
resource sets before and after any restriction of the raw state. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_raw_seed_resource_sizes
    (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (hℓ:∀i,1≤ℓ i) (hℓmax:∀i,ℓ i≤K):
    ∀i (c:longRawHubCandidates (U:=U) π d m ℓ i),
      2≤(longRawHubResources (U:=U) π d m ℓ i c).card ∧
      (longRawHubResources (U:=U) π d m ℓ i c).card≤2*max (m+1) K :=by
  intro i c
  cases i with
  | none =>
    have hh:=typed_marked_seed_resource_size c
    dsimp only [longRawHubResources,longRawSeedResources,longMixedSeedResources]
    constructor
    · convert hh.1 using 1 <;> congr 3 <;> exact Subsingleton.elim _ _
    · have h:=hh.2.trans (Nat.mul_le_mul_left 2 (le_max_left (m+1) K))
      convert h using 1 <;> congr 3 <;> exact Subsingleton.elim _ _
  | some i =>
    have hh:=ordered_ordinary_seed_resource_size (hℓ i) c
    change 2≤((orderedOrdinaryResources c).map ordinaryMarkedResourceEmbedding).card ∧
      ((orderedOrdinaryResources c).map ordinaryMarkedResourceEmbedding).card≤2*max (m+1) K
    rw [Finset.card_map]
    exact ⟨hh.1,hh.2.trans (Nat.mul_le_mul_left 2 ((hℓmax i).trans (le_max_right _ _)))⟩
end Oberwolfach
