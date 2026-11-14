module

public import Oberwolfach.MixedFreshBoundaryInsideRootsNamed

@[expose] public section
/-! Structural and weighted input for a fresh mixed-factor sample, packaged
without strengthening any theorem hypothesis. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W J K:Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]

structure MixedFreshParentDataInsideRoots (γ κ b B ε η:ℝ) (Q F:SimpleGraph V) (P B₀:SimpleGraph W)
    (e:V↪W) (T:J→Finset V) (S U:K→Finset W) where
  mapped_host:Q.map e≤P
  endpoint_disjoint:∀k,Disjoint (S k) (U k)
  hub_size:∀j,κ*Fintype.card V≤((T j).card:ℝ)
  rim_conflict:∀v,(F.degree v:ℝ)≤ε*Fintype.card V
  physical_conflict:∀w,(B₀.degree w:ℝ)≤ε*Fintype.card W
  hub_neighborhoods:∀j,∀X:Finset V,X⊆T j→X.card≤3→
    γ*Fintype.card V≤((common (T j) X (fun x=>Q.neighborFinset x)).card:ℝ)
  endpoint_neighborhoods:∀k,EndpointNeighbourCounts P B₀ (S k) (U k) (γ*Fintype.card W)
  hub_weight:∀j,LocalOrdinaryCycle Q F (T j) 3→ℝ
  endpoint_weight:∀k,EndpointTriangle P B₀ (S k) (U k)→ℝ
  hub_weight_bounds:∀j C,b/(Fintype.card V:ℝ)^2≤hub_weight j C ∧ hub_weight j C≤B/(Fintype.card V:ℝ)^2
  endpoint_weight_bounds:∀k C,b/(Fintype.card W:ℝ)^2≤endpoint_weight k C ∧ endpoint_weight k C≤B/(Fintype.card W:ℝ)^2
  hub_weight_load:∀j,∀v∈T j,|1-hypergraphWeightedDegree localOrdinaryVertices (hub_weight j) v|≤η
  endpoint_weight_load:∀k,∀w∈S k∪U k,|1-hypergraphWeightedDegree endpointTriangleVertices (endpoint_weight k) w|≤η

theorem mixed_fresh_boundary_probability_from_inside_parent
    (γ κ b B:ℝ) (hγ:0<γ) (hκ:0<κ) (hb:0<b) (hB:0≤B):
    ∃ε η ζ:ℝ,0<ε ∧ 0<η ∧ 0<ζ ∧
      ∀(p:ℝ) (hp:0<p) (hp1:p≤1) (ρ:ℝ) (hρ:0<ρ) (q:ℕ),∃N:ℕ,
      ∀(V W J K E:Type) [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
        [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K] [Fintype E] [DecidableEq E],
        N≤Fintype.card V→Fintype.card J≤(Fintype.card V)^2→Fintype.card K≤(Fintype.card W)^2→
      ∀(Q F:SimpleGraph V) (P B₀:SimpleGraph W) (e:V↪W) (T:J→Finset V) (S U:K→Finset W)
        (f:J→V↪E) (g:K→W↪E) (data:MixedFreshParentDataInsideRoots γ κ b B ε η Q F P B₀ e T S U),
      1-1/(Fintype.card V:ℝ)^q≤
        (FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp.le hp1)).probability
          (MixedFreshBoundaryAvoidingEvent p ρ ζ Q F P B₀ e T S U f g data.endpoint_disjoint):=by
  obtain ⟨ε,η,ζ,hε,hη,hζ,h⟩:=mixed_fresh_boundary_inside_roots_named_event γ κ b B hγ hκ hb hB
  refine ⟨ε,η,ζ,hε,hη,hζ,?_⟩
  intro p hp hp1 ρ hρ q
  obtain ⟨N,hN⟩:=h p hp hp1 ρ hρ q
  refine ⟨N,?_⟩
  intro V W J K E _ _ _ _ _ _ _ _ _ _ hn hJ hK Q F P B₀ e T S U f g data
  exact hN V W J K E hn hJ hK Q F P B₀ e data.mapped_host T S U f g data.endpoint_disjoint
    data.hub_size data.rim_conflict data.physical_conflict data.hub_neighborhoods data.endpoint_neighborhoods
    data.hub_weight data.endpoint_weight data.hub_weight_bounds data.endpoint_weight_bounds
    data.hub_weight_load data.endpoint_weight_load
end Oberwolfach
