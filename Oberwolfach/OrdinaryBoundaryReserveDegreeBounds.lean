module

public import Oberwolfach.OrdinaryBoundaryReserveJointEvent
public import Oberwolfach.OrdinaryPhysicalDegreeDomains

@[expose] public section
/-! A good physical boundary sample has uniformly bounded rim, spoke-row,
and spoke-column degrees in the actual reserved subgraphs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_physical_column_degree (G:SimpleGraph (V⊕U)) (u:U):
    (ordinaryPhysicalRimDomain ∩ G.neighborFinset (Sum.inr u)).card=
      (Finset.univ.filter (fun v=>G.Adj (Sum.inl v) (Sum.inr u))).card:=by
  have he:ordinaryPhysicalRimDomain ∩ G.neighborFinset (Sum.inr u)=
      (Finset.univ.filter (fun v=>G.Adj (Sum.inl v) (Sum.inr u))).image Sum.inl:=by
    ext z
    cases z with
    | inl v=>simp [ordinaryPhysicalRimDomain,SimpleGraph.mem_neighborFinset,SimpleGraph.adj_comm]
    | inr w=>simp [ordinaryPhysicalRimDomain]
  rw [he,Finset.card_image_of_injective _ Sum.inl_injective]

theorem ordinary_boundary_reserve_degree_bounds
    (Q:SimpleGraph V) (H:V→U→Prop) (I:Finset V) (J:Finset U) (τ ε:ℝ)
    (hτ:0≤τ) (σ:Sym2 (V⊕U)→Bool) (hgood:OrdinaryBoundaryReserveGood Q H I J τ ε σ):
    let R:=retainedGraph (ordinaryBoundaryGraph Q H I J) σ;
    (∀v,((R.comap Sum.inl).degree v:ℝ)≤(τ+ε)*Fintype.card (V⊕U)) ∧
    (∀v,((Finset.univ.filter (fun u=>R.Adj (Sum.inl v) (Sum.inr u))).card:ℝ)≤(τ+ε)*Fintype.card (V⊕U)) ∧
    (∀u,((Finset.univ.filter (fun v=>R.Adj (Sum.inl v) (Sum.inr u))).card:ℝ)≤(τ+ε)*Fintype.card (V⊕U)):=by
  intro R
  let B:=ordinaryBoundaryGraph Q H I J
  have htotal (x:V⊕U):(R.degree x:ℝ)≤(τ+ε)*Fintype.card (V⊕U):=by
    have hn:(B.degree x:ℝ)≤Fintype.card (V⊕U):=by
      rw [←SimpleGraph.card_neighborFinset_eq_degree]
      exact_mod_cast (Finset.card_le_univ (B.neighborFinset x))
    have ht:=abs_lt.mp (hgood.1 x)
    have hu:=mul_le_mul_of_nonneg_left hn hτ
    nlinarith only [ht.2,hu]
  refine ⟨?_,?_,?_⟩
  · intro v
    have hs:((ordinaryPhysicalRimDomain∩R.neighborFinset (Sum.inl v)).card:ℝ)≤R.degree (Sum.inl v):=by
      rw [←SimpleGraph.card_neighborFinset_eq_degree]
      exact_mod_cast (Finset.card_le_card (Finset.inter_subset_right : _))
    rw [ordinary_physical_left_degree] at hs
    exact hs.trans (htotal _)
  · intro v
    have hs:((ordinaryPhysicalHubDomain∩R.neighborFinset (Sum.inl v)).card:ℝ)≤R.degree (Sum.inl v):=by
      rw [←SimpleGraph.card_neighborFinset_eq_degree]
      exact_mod_cast (Finset.card_le_card (Finset.inter_subset_right : _))
    rw [ordinary_physical_right_degree] at hs
    exact hs.trans (htotal _)
  · intro u
    have hs:((ordinaryPhysicalRimDomain∩R.neighborFinset (Sum.inr u)).card:ℝ)≤R.degree (Sum.inr u):=by
      rw [←SimpleGraph.card_neighborFinset_eq_degree]
      exact_mod_cast (Finset.card_le_card (Finset.inter_subset_right : _))
    rw [ordinary_physical_column_degree] at hs
    exact hs.trans (htotal _)
end Oberwolfach
