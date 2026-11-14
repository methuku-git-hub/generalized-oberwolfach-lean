module

public import Oberwolfach.MixedFreshBoundaryEventDefinition

@[expose] public section
/-! The named event has the same high-probability estimate as its original
pointwise factor formulation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 6500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem mixed_fresh_boundary_avoiding_named_event (γ κ b B:ℝ) (hγ:0<γ) (hκ:0<κ) (hb:0<b) (hB:0≤B):
    ∃ ε η ζ:ℝ,0<ε ∧ 0<η ∧ 0<ζ ∧
    ∀ (p:ℝ) (hp:0<p) (hp1:p≤1) (ρ:ℝ) (hρ:0<ρ) (q:ℕ),∃ N:ℕ,
    ∀ (V W J K E:Type) [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
      [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K] [Fintype E] [DecidableEq E],
      N≤Fintype.card V→Fintype.card J≤(Fintype.card V)^2→Fintype.card K≤(Fintype.card W)^2→
    ∀ (Q F:SimpleGraph V) (P B₀:SimpleGraph W) (e:V↪W),Q.map e≤P→
    ∀ (T:J→Finset V) (S U:K→Finset W) (f:J→V↪E) (g:K→W↪E)
      (hSU:∀ k,Disjoint (S k) (U k)),
      (∀ j,κ*Fintype.card V≤((T j).card:ℝ))→
      (∀ v,(F.degree v:ℝ)≤ε*Fintype.card V)→
      (∀ w,(B₀.degree w:ℝ)≤ε*Fintype.card W)→
      (∀ j,∀ X:Finset V,X.card≤3→
        γ*Fintype.card V≤((common (T j) X (fun x=>Q.neighborFinset x)).card:ℝ))→
      (∀ k,EndpointNeighbourCounts P B₀ (S k) (U k) (γ*Fintype.card W))→
    ∀ (wt:∀ j,LocalOrdinaryCycle Q F (T j) 3→ℝ)
      (we:∀ k,EndpointTriangle P B₀ (S k) (U k)→ℝ),
      (∀ j C,b/(Fintype.card V:ℝ)^2≤wt j C ∧ wt j C≤B/(Fintype.card V:ℝ)^2)→
      (∀ k C,b/(Fintype.card W:ℝ)^2≤we k C ∧ we k C≤B/(Fintype.card W:ℝ)^2)→
      (∀ j,∀ v∈T j,|1-hypergraphWeightedDegree localOrdinaryVertices (wt j) v|≤η)→
      (∀ k,∀ w∈S k∪U k,|1-hypergraphWeightedDegree endpointTriangleVertices (we k) w|≤η)→
    1-1/(Fintype.card V:ℝ)^q≤
      (FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp.le hp1)).probability
      (MixedFreshBoundaryAvoidingEvent p ρ ζ Q F P B₀ e T S U f g hSU):=by
  obtain ⟨ε,η,ζ,hε,hη,hζ,h⟩:=mixed_fresh_boundary_factors_avoiding γ κ b B hγ hκ hb hB
  exact ⟨ε,η,ζ,hε,hη,hζ,h⟩
end Oberwolfach
