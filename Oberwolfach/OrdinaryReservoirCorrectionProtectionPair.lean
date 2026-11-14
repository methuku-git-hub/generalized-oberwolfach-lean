module

public import Oberwolfach.OrdinaryReservoirProtectedCorrection

@[expose] public section
/-! The reservoir rows and hubs may be added to the protected pair before
correction, with exactly their finite cardinality as the extra cost. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_reservoir_correction_protection_pair
    (Q:SimpleGraph V) (H:V→U→Prop) (K:Finset (Sym2 V⊕(V×U)))
    (Z:Finset V) (B:Finset U) (a b:ℕ) (hK:K⊆ordinaryHostResources Q H)
    (hrows:(ordinaryResourceRows K).card≤a) (hhubs:(ordinaryResourceHubs K).card≤b):
    let T:=Z∪ordinaryResourceRows K;let B':=B∪ordinaryResourceHubs K;
    Z⊆T ∧ B⊆B' ∧ T.card≤Z.card+a ∧ B'.card≤B.card+b ∧
    ∀(JQ:SimpleGraph V) (JH:V→U→Prop),
      (∀v∈T,∀w∈T,¬JQ.Adj v w)→
      (∀v u,JH v u→¬(v∈T ∧ u∈B'))→
      K⊆ordinaryHostResources (Q\JQ) (fun v u=>H v u∧¬JH v u) ∧
      (∀v∈Z,∀w∈Z,¬JQ.Adj v w) ∧
      (∀v u,JH v u→¬(v∈Z ∧ u∈B)):=by
  intro T B'
  have hZT:Z⊆T:=Finset.subset_union_left
  have hBB:B⊆B':=Finset.subset_union_left
  have hr:ordinaryResourceRows K⊆T:=Finset.subset_union_right
  have hh:ordinaryResourceHubs K⊆B':=Finset.subset_union_right
  have hcardT:T.card≤Z.card+a:=(Finset.card_union_le _ _).trans (Nat.add_le_add_left hrows _)
  have hcardB:B'.card≤B.card+b:=(Finset.card_union_le _ _).trans (Nat.add_le_add_left hhubs _)
  refine ⟨hZT,hBB,hcardT,hcardB,?_⟩
  intro JQ JH hJQ hJH
  refine ⟨ordinary_reservoir_survives_protected_correction Q JQ H JH K T B' hK hr hh hJQ hJH,?_,?_⟩
  · intro v hv w hw
    exact hJQ v (hZT hv) w (hZT hw)
  · intro v u h hh'
    exact hJH v u h ⟨hZT hh'.1,hBB hh'.2⟩
end Oberwolfach
