module

public import Oberwolfach.MarkedFixedVortexSizes

@[expose] public section
/-! The ambient-to-inner comparisons for the actual fixed vortex, retaining
the separate vertex and hub rounding recurrences. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε ρ₀:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_fixed_ambient_size_fields
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V)
    (hD:(Fintype.card V:ℝ)/2≤D) (hr:0<ρ₀)
    (hrlo:ρ₀ ≤ initialIndexDensity U D) (hrhi:initialIndexDensity U D ≤ 1)
    (hb:0≤β) (hb1:β≤1/4) (he:0<ε) (hm:0<m)
    (i:ℕ) (hi:i<Q.length):
    (ε/2)*(Fintype.card (markedVortexVertexType Q i):ℝ)≤(markedVortexInnerVertices Q i).card ∧
    (ρ₀/8)*((markedVortexInnerVertices Q i).card:ℝ)≤(markedVortexInnerHubs Q i).card ∧
    Fintype.card (markedVortexHubType Q i)≤Fintype.card (markedVortexVertexType Q i):=by
  have hP:Fintype.card (markedVortexVertexType Q i)=(Q.vertices i).card:=by
    change Fintype.card (Q.extendedVertices i)=(Q.vertices i).card
    rw [Fintype.card_coe,Q.extendedVertices_eq hi.le]
  have hH:Fintype.card (markedVortexHubType Q i)=(Q.indices i).card:=by
    change Fintype.card (Q.extendedIndices i)=(Q.indices i).card
    rw [Fintype.card_coe,Q.extendedIndices_eq hi.le]
  obtain ⟨hI,_,hJ,_⟩:=marked_vortex_inner_cardinalities Q i
  rw [Q.extendedVertices_eq (by omega : i+1≤Q.length)] at hI
  rw [Q.extendedIndices_eq (by omega : i+1≤Q.length)] at hJ
  have hIl:ε/2*((Q.vertices i).card:ℝ)≤(Q.vertices (i+1)).card:=by
    have hh:=(Q.consecutive_size_bounds he hm hi).1
    nlinarith
  have hJl:=Q.index_size_lower hreg hn hD hr hrlo hb hb1 (by omega : i+1≤Q.length)
  have hDp:0<D:=by
    have hn':(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
    exact_mod_cast (show (0:ℝ)<D by linarith)
  have hHu:=Q.index_size_upper hreg hn hDp he.le hrhi hi.le
  refine ⟨?_,?_,?_⟩
  · rw [hP,hI]; exact hIl
  · rw [hI,hJ]; exact hJl
  · rw [hH,hP]; omega
end Oberwolfach
