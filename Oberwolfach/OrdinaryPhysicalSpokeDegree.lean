module

public import Oberwolfach.OrdinaryBoundaryGraph

@[expose] public section
/-! Spoke entries of any physical graph at a fixed row or column are bounded
by the degree of the corresponding physical vertex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_physical_spoke_row_le_degree (R:SimpleGraph (V⊕U)) (v:V):
    (Finset.univ.filter (fun u=>R.Adj (Sum.inl v) (Sum.inr u))).card≤R.degree (Sum.inl v):=by
  let T:=Finset.univ.filter (fun u=>R.Adj (Sum.inl v) (Sum.inr u))
  have hsub:T.image Sum.inr⊆R.neighborFinset (Sum.inl v):=by
    intro x hx
    obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hx
    exact (R.mem_neighborFinset _ _).mpr (Finset.mem_filter.mp hu).2
  calc
    T.card=(T.image Sum.inr).card:=(Finset.card_image_of_injective T Sum.inr_injective).symm
    _≤(R.neighborFinset (Sum.inl v)).card:=Finset.card_le_card hsub
    _=R.degree (Sum.inl v):=SimpleGraph.card_neighborFinset_eq_degree R _

theorem ordinary_physical_spoke_column_le_degree (R:SimpleGraph (V⊕U)) (u:U):
    (Finset.univ.filter (fun v=>R.Adj (Sum.inl v) (Sum.inr u))).card≤R.degree (Sum.inr u):=by
  let T:=Finset.univ.filter (fun v=>R.Adj (Sum.inl v) (Sum.inr u))
  have hsub:T.image Sum.inl⊆R.neighborFinset (Sum.inr u):=by
    intro x hx
    obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hx
    exact (R.mem_neighborFinset _ _).mpr ((Finset.mem_filter.mp hv).2.symm)
  calc
    T.card=(T.image Sum.inl).card:=(Finset.card_image_of_injective T Sum.inl_injective).symm
    _≤(R.neighborFinset (Sum.inr u)).card:=Finset.card_le_card hsub
    _=R.degree (Sum.inr u):=SimpleGraph.card_neighborFinset_eq_degree R _
theorem ordinary_physical_rim_row_le_degree (R:SimpleGraph (V⊕U)) (v:V):
    (Finset.univ.filter (fun w=>R.Adj (Sum.inl v) (Sum.inl w))).card≤R.degree (Sum.inl v):=by
  let T:=Finset.univ.filter (fun w=>R.Adj (Sum.inl v) (Sum.inl w))
  have hsub:T.image Sum.inl⊆R.neighborFinset (Sum.inl v):=by
    intro x hx
    obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hx
    exact (R.mem_neighborFinset _ _).mpr (Finset.mem_filter.mp hw).2
  calc
    T.card=(T.image Sum.inl).card:=(Finset.card_image_of_injective T Sum.inl_injective).symm
    _≤(R.neighborFinset (Sum.inl v)).card:=Finset.card_le_card hsub
    _=R.degree (Sum.inl v):=SimpleGraph.card_neighborFinset_eq_degree R _
end Oberwolfach
