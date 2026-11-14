module

public import Oberwolfach.MarkedFixedVortexAmbientBounds
public import Oberwolfach.MarkedActiveAmbientComparisons

@[expose] public section
/-! Uniform minimum-size and ambient-size prerequisites for the actual fixed
vortex domains. The threshold is chosen before the graph and vortex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_fixed_vortex_event_size_inputs
    (β ε ρ₀:ℝ) (hb:0≤β) (hb1:β≤1/4) (he:0<ε) (he1:ε<1/4)
    (hr:0<ρ₀) (M:ℕ):
    ∃ m₀:ℕ,1≤m₀ ∧ ∀ (V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (G:SimpleGraph V) (D m:ℕ),G.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀ ≤ initialIndexDensity U D→initialIndexDensity U D≤1→
      m₀≤m→∀ Q:Vortex U G D β ε m,∀ i,i<Q.length→
      let K:=1+1/(ε/2)+1/((ε/2)*(ρ₀/8))
      1≤K ∧
      (M:ℝ)≤(1-ε)*((markedVortexInnerVertices Q i).card:ℝ) ∧
      (M:ℝ)≤(1-ε)*((markedVortexInnerHubs Q i).card:ℝ) ∧
      (Fintype.card (markedVortexVertexType Q i):ℝ)≤K*(markedVortexInnerVertices Q i).card ∧
      (Fintype.card (markedVortexHubType Q i):ℝ)≤K*(markedVortexInnerVertices Q i).card ∧
      (Fintype.card (markedVortexVertexType Q i):ℝ)≤K*(markedVortexInnerHubs Q i).card:=by
  have he' : ε<1:=by linarith
  have hiota:0<ε/2:=by positivity
  have homega:0<ρ₀/8:=by positivity
  obtain ⟨N,hN⟩:=marked_active_minimum_threshold ε (ε/2) (ρ₀/8) he' hiota homega M
  refine ⟨max N 1,le_max_right _ _,?_⟩
  intro V U _ _ _ _ G D m hreg hn hD hrlo hrhi hm Q i hi K
  have hmpos:0<m:=by omega
  obtain ⟨hI,hJ,hun⟩:=marked_vortex_fixed_ambient_size_fields Q hreg hn hD hr hrlo hrhi hb hb1 he hmpos i hi
  have hinner:((ε/2)*(m:ℝ))≤(markedVortexInnerVertices Q i).card:=by
    obtain ⟨hcard,_,_,_⟩:=marked_vortex_inner_cardinalities Q i
    rw [hcard,Q.extendedVertices_eq (by omega : i+1≤Q.length)]
    have hh:=Q.vertices_lower (by omega : i+1≤Q.length)
    nlinarith
  have hmins:=hN m (markedVortexInnerVertices Q i).card (markedVortexInnerHubs Q i).card
    (by omega) hinner hJ
  have hUP:(Fintype.card (markedVortexHubType Q i):ℝ)≤Fintype.card (markedVortexVertexType Q i):=by exact_mod_cast hun
  have hbounds:=marked_active_ambient_comparisons
    (Fintype.card (markedVortexVertexType Q i)) (Fintype.card (markedVortexHubType Q i))
    (markedVortexInnerVertices Q i).card (markedVortexInnerHubs Q i).card (ε/2) (ρ₀/8)
    hiota homega (by positivity) (by positivity) hUP hI hJ
  exact ⟨hbounds.1,hmins.1,hmins.2,hbounds.2.1,hbounds.2.2.1,hbounds.2.2.2⟩
end Oberwolfach
