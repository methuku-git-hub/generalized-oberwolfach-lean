module

public import Oberwolfach.OrdinaryTriangleSeparatedCoverRate
public import Oberwolfach.MarkedFixedVortexSizes
public import Oberwolfach.VortexProtectedGeometry

@[expose] public section
/-! The separated root-cover cost is small at every actual vortex level.
The load is selected after the vortex ratio and before the host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_vortex_cover_rate
    (ε δ cap:ℝ) (hε:0<ε) (hδ:0<δ) (hcap:0<cap) (hεsmall:ε≤δ/12):
    ∃a:ℝ,0<a ∧ a≤cap ∧
    ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (P:SimpleGraph V) (D m:ℕ) (β:ℝ) (Q:Vortex U P D β ε m),0<m→
    ∀i,i<Q.length→(markedVortexInnerHubs Q i).card≤(markedVortexInnerVertices Q i).card→
      18*a*Fintype.card (markedVortexVertexType Q i)+
        3*((markedVortexDeeperHubs Q i).card+(markedVortexDeeperVertices Q i).card)≤δ*(markedVortexInnerVertices Q i).card ∧
      9*a*Fintype.card (markedVortexVertexType Q i)+3*((markedVortexDeeperVertices Q i).card:ℝ)≤δ*(markedVortexInnerVertices Q i).card :=by
  obtain ⟨a,ha,hacap,hrate⟩:=ordinary_triangle_separated_cover_rate ε δ cap hε hδ hcap hεsmall
  refine ⟨a,ha,hacap,?_⟩
  intro V U _ _ _ _ P D m β Q hm i hi hBI
  have hparent:Fintype.card (markedVortexVertexType Q i)=(Q.vertices i).card:=by
    change Fintype.card (Q.extendedVertices i)=(Q.vertices i).card
    rw [Fintype.card_coe,Q.extendedVertices_eq hi.le]
  have hinner:(markedVortexInnerVertices Q i).card=(Q.vertices (i+1)).card:=by
    rw [(marked_vortex_inner_cardinalities Q i).1,Q.extendedVertices_eq (by omega:i+1≤Q.length)]
  have hsize:ε*(Fintype.card (markedVortexVertexType Q i):ℝ)/2≤(markedVortexInnerVertices Q i).card:=by
    rw [hparent,hinner]
    have hh:=(Q.consecutive_size_bounds hε hm hi).1
    nlinarith
  have hgeom:=marked_vortex_fixed_active_geometry Q hε.le i
  have hW:((markedVortexDeeperHubs Q i).card:ℝ)≤ε*(markedVortexInnerVertices Q i).card:=by
    have hBI':((markedVortexInnerHubs Q i).card:ℝ)≤(markedVortexInnerVertices Q i).card:=by exact_mod_cast hBI
    exact hgeom.2.2.2.1.trans (mul_le_mul_of_nonneg_left hBI' hε.le)
  exact hrate (Fintype.card (markedVortexVertexType Q i)) (markedVortexInnerVertices Q i).card
    (markedVortexDeeperVertices Q i).card (markedVortexDeeperHubs Q i).card
    (by positivity) (by positivity) (by positivity) (by positivity) hsize hgeom.2.2.1 hW
end Oberwolfach
