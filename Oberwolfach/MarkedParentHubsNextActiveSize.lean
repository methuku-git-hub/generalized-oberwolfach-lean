module

public import Oberwolfach.MarkedVortexActiveGeometryBounds
public import Oberwolfach.MarkedVortexActiveDomainEquivalences

@[expose] public section
/-! Parent hubs are bounded by a fixed multiple of the next active vertex
set; the multiple depends on the already fixed vortex ratio. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

theorem marked_parent_hubs_next_active_size
    (ρ₀:ℝ) (hρ₀:0<ρ₀) (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V)
    (hDhalf:(Fintype.card V:ℝ)/2≤D) (hDpos:0<D)
    (hρlo:ρ₀≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
    (hb:0≤β) (hb1:β≤1/4) (he:0<ε) (he1:ε≤1/4) (hm:0<m)
    (i:ℕ) (hi:i<Q.length):
    (Fintype.card (markedVortexHubType Q i):ℝ)≤
      (4/ε)*Fintype.card ↥((Finset.univ\markedVortexInnerVertices Q (i+1)):Finset (markedVortexVertexType Q (i+1))) :=by
  have hh:=Q.index_size_upper hreg hn hDpos he.le hρhi hi.le
  have hz:(Fintype.card (markedVortexHubType Q i):ℝ)≤(Q.vertices i).card:=by
    change (Fintype.card ↥(Q.extendedIndices i):ℝ)≤(Q.vertices i).card
    rw [Fintype.card_coe,Q.extendedIndices_eq hi.le]
    exact_mod_cast (by omega : (Q.indices i).card≤(Q.vertices i).card)
  have hnext:ε*(Q.vertices i).card/2≤((Q.vertices (i+1)).card:ℝ):=(Q.consecutive_size_bounds he hm hi).1
  have ha:=(marked_vortex_active_geometry_bounds Q ρ₀ hρ₀ hreg hn hDhalf hρlo hρhi hb hb1 he.le he1 (i+1) (by omega)).1
  have hequiv:Fintype.card ↥((Finset.univ\markedVortexInnerVertices Q (i+1)):Finset (markedVortexVertexType Q (i+1)))=
      (Q.extendedVertices (i+1)\Q.extendedVertices (i+2)).card:=by
    have h:=Fintype.card_congr (markedVortexActiveVertexEquiv Q (i+1))
    change Fintype.card ↥((Finset.univ\markedVortexInnerVertices Q (i+1)):Finset (markedVortexVertexType Q (i+1)))=
      Fintype.card ↥(Q.extendedVertices (i+1)\Q.extendedVertices (i+1+1)) at h
    simpa only [Fintype.card_coe,Nat.add_assoc,show 1+1=2 by omega] using h
  rw [Q.extendedVertices_eq (by omega:i+1≤Q.length)] at ha
  rw [hequiv]
  have hzmul:=mul_le_mul_of_nonneg_left hz he.le
  have hv:(Fintype.card (markedVortexHubType Q i):ℝ)*ε≤4*(Q.extendedVertices (i+1)\Q.extendedVertices (i+2)).card:=by
    rw [Q.extendedVertices_eq (by omega:i+1≤Q.length)]
    simp only [Nat.add_assoc,show 1+1=2 by omega] at ha
    nlinarith [hzmul]
  calc
    (Fintype.card (markedVortexHubType Q i):ℝ) ≤ (4*(Q.extendedVertices (i+1)\Q.extendedVertices (i+2)).card)/ε := (le_div_iff₀ he).2 hv
    _ = 4/ε*(Q.extendedVertices (i+1)\Q.extendedVertices (i+2)).card := by ring
end Oberwolfach
