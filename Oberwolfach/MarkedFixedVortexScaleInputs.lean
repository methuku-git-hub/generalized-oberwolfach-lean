module

public import Oberwolfach.MarkedFixedVortexReferenceDegreeInputs
public import Oberwolfach.MarkedFixedVortexAmbientBounds

@[expose] public section
/-! The reference event may use the actual parent vertex order as its scale.
The inner vertex and hub domains fit that scale and it contracts at the
vortex's original rate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε ρ₀:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_reference_scale_inputs
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V)
    (hD:(Fintype.card V:ℝ)/2≤D) (hr:0<ρ₀)
    (hrlo:ρ₀ ≤ initialIndexDensity U D) (hrhi:initialIndexDensity U D ≤ 1)
    (hb:0≤β) (hb1:β≤1/4) (he:0<ε) (hm:0<m)
    (i:ℕ) (hi:i<Q.length):
    let W:=markedVortexVertexType Q
    let Z:=markedVortexHubType Q
    let I:=markedVortexInnerVertices Q
    let J:=markedVortexInnerHubs Q
    (I i).card≤Fintype.card (W i) ∧ (J i).card≤Fintype.card (W i) ∧
    Fintype.card (Z i)≤Fintype.card (W i) ∧
    (Fintype.card (W (i+1)):ℝ)≤ε*Fintype.card (W i):=by
  intro W Z I J
  have hinner: (I i).card≤Fintype.card (W i):=Finset.card_le_univ _
  have hhub: (J i).card≤Fintype.card (Z i):=Finset.card_le_univ _
  have hamb: Fintype.card (Z i)≤Fintype.card (W i):=
    (marked_vortex_fixed_ambient_size_fields Q hreg hn hD hr hrlo hrhi hb hb1 he hm i hi).2.2
  have hstep:= (Q.extended_successor_size_bounds he.le i).1
  have hc0:Fintype.card (W i)=(Q.extendedVertices i).card:=by
    change Fintype.card (Q.extendedVertices i)=(Q.extendedVertices i).card
    exact Fintype.card_coe _
  have hc1:Fintype.card (W (i+1))=(Q.extendedVertices (i+1)).card:=by
    change Fintype.card (Q.extendedVertices (i+1))=(Q.extendedVertices (i+1)).card
    exact Fintype.card_coe _
  refine ⟨hinner,hhub.trans hamb,hamb,?_⟩
  rw [hc0,hc1]
  exact hstep
end Oberwolfach
