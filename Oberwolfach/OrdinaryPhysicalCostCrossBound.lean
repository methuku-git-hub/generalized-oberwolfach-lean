module

public import Oberwolfach.OrdinaryProtectedInnerPersistence
public import Oberwolfach.OrdinaryCrossBalanceDeletionTransferAt

@[expose] public section
/-! The recorded physical degree of a deletion bounds its cross discrepancy
on any smaller pair of domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_physical_cost_cross_bound
    (R:SimpleGraph V) (S:V→U→Prop) (X I:Finset V) (Z J:Finset U)
    (hIX:I⊆X) (hJZ:J⊆Z) (v:V) (hvX:v∈X) (D:ℝ)
    (hdeg:∀w:V⊕U,((spanningRestriction (ordinaryPhysicalGraph R S)
      (ordinaryInnerVertices X Z)).degree w:ℝ)≤D):
    |((R.neighborFinset v∩I).card:ℝ)-2*(J.filter (S v)).card|≤2*D :=by
  let C:=spanningRestriction (ordinaryPhysicalGraph R S) (ordinaryInnerVertices X Z)
  let Rim:=R.neighborFinset v∩I
  let Sp:=J.filter (S v)
  have hD:0≤D:=le_trans (by positivity : (0:ℝ)≤(C.degree (Sum.inl v):ℝ)) (hdeg (Sum.inl v))
  have hRim:Rim.image (Sum.inl:V→V⊕U)⊆C.neighborFinset (Sum.inl v):=by
    intro y hy
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hy
    have hr:R.Adj v x:=(R.mem_neighborFinset v x).mp (Finset.mem_inter.mp hx).1
    have hxI:x∈I:=(Finset.mem_inter.mp hx).2
    apply (C.mem_neighborFinset _ _).mpr
    exact (spanningRestriction_adj _ _ _ _).mpr ⟨hr,(ordinaryInnerVertices_left X Z v).mpr hvX,(ordinaryInnerVertices_left X Z x).mpr (hIX hxI)⟩
  have hSp:Sp.image (Sum.inr:U→V⊕U)⊆C.neighborFinset (Sum.inl v):=by
    intro y hy
    obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hy
    have huJ:u∈J:=(Finset.mem_filter.mp hu).1
    have hs:S v u:=(Finset.mem_filter.mp hu).2
    apply (C.mem_neighborFinset _ _).mpr
    exact (spanningRestriction_adj _ _ _ _).mpr ⟨hs,(ordinaryInnerVertices_left X Z v).mpr hvX,(ordinaryInnerVertices_right X Z u).mpr (hJZ huJ)⟩
  have hRimCard:(Rim.card:ℝ)≤D:=by
    have hh:=Finset.card_le_card hRim
    rw [Finset.card_image_of_injective _ Sum.inl_injective,SimpleGraph.card_neighborFinset_eq_degree] at hh
    have hr:(Rim.card:ℝ)≤(C.degree (Sum.inl v):ℝ):=by exact_mod_cast hh
    exact hr.trans (hdeg (Sum.inl v))
  have hSpCard:(Sp.card:ℝ)≤D:=by
    have hh:=Finset.card_le_card hSp
    rw [Finset.card_image_of_injective _ Sum.inr_injective,SimpleGraph.card_neighborFinset_eq_degree] at hh
    have hs:(Sp.card:ℝ)≤(C.degree (Sum.inl v):ℝ):=by exact_mod_cast hh
    exact hs.trans (hdeg (Sum.inl v))
  have hr0:0≤(Rim.card:ℝ):=by positivity
  have hs0:0≤(Sp.card:ℝ):=by positivity
  change |(Rim.card:ℝ)-2*(Sp.card:ℝ)|≤2*D
  apply abs_le.mpr
  constructor <;> linarith only [hRimCard,hSpCard,hr0,hs0,hD]
end Oberwolfach
