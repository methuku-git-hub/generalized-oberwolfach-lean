module

public import Oberwolfach.MarkedFixedVortexAmbientBounds

@[expose] public section
/-! Each actual fixed parent vortex subtype has the hub-density lower bound
required by the joint reference event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε ρ₀:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_fixed_parent_hub_density
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V)
    (hD:(Fintype.card V:ℝ)/2≤D) (hr:0<ρ₀)
    (hrlo:ρ₀ ≤ initialIndexDensity U D) (hb:0≤β) (hb1:β≤1/4)
    (i:ℕ) (hi:i≤Q.length):
    (ρ₀/8)*(Fintype.card (markedVortexVertexType Q i):ℝ)≤
      (Fintype.card (markedVortexHubType Q i):ℝ):=by
  have hW:Fintype.card (markedVortexVertexType Q i)=(Q.vertices i).card:=by
    change Fintype.card (Q.extendedVertices i)=(Q.vertices i).card
    rw [Fintype.card_coe,Q.extendedVertices_eq hi]
  have hZ:Fintype.card (markedVortexHubType Q i)=(Q.indices i).card:=by
    change Fintype.card (Q.extendedIndices i)=(Q.indices i).card
    rw [Fintype.card_coe,Q.extendedIndices_eq hi]
  rw [hW,hZ]
  exact Q.index_size_lower hreg hn hD hr hrlo hb hb1 hi
end Oberwolfach
