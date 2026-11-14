module

public import Oberwolfach.MarkedVortexPreselectReservedProperty

@[expose] public section
/-! The terminal and first-inner size bounds required for corrected-vortex
iteration follow from the actual vortex and the earlier absorber scale. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_vortex_terminal_decomposition_geometry
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [Nonempty V] [DecidableEq U]
    (G:SimpleGraph V) (D m:ℕ) (β ε εabs:ℝ) (Q:Vortex U G D β ε m)
    (L size f:ℕ) (hL:L+1=Q.length)
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V) (hD:0<D)
    (hρhi:initialIndexDensity U D≤1) (hε:0≤ε) (hεabs:ε≤εabs) (hsize:2*m≤size):
    (Q.extendedVertices (L+1)).card+(Q.extendedIndices (L+1)).card≤size ∧
    ((Q.extendedVertices 1).card:ℝ)≤εabs*Fintype.card V+f ∧
    ((Q.extendedIndices 1).card:ℝ)≤εabs*Fintype.card V+f :=by
  have hcap:=marked_vortex_reserved_capacity_fields Q hreg hn hD hρhi hε εabs hεabs L hL
    (Function.Embedding.refl (markedVortexVertexType Q L)) (Function.Embedding.refl (markedVortexHubType Q L))
  obtain ⟨hI0,_,hJ0,_⟩:=marked_vortex_inner_cardinalities Q 0
  obtain ⟨hIL,_,hJL,_⟩:=marked_vortex_inner_cardinalities Q L
  have hcard0:Fintype.card (markedVortexVertexType Q 0)=Fintype.card V:=by
    change Fintype.card ↥(Q.extendedVertices 0)=Fintype.card V
    rw [Fintype.card_coe,Q.extendedVertices_eq (Nat.zero_le _),Q.initial,Finset.card_univ]
  have hV:((Q.extendedVertices 1).card:ℝ)≤εabs*Fintype.card V+f:=by
    have hh:=hcap.1
    rw [hI0,hcard0] at hh
    have hf:(0:ℝ)≤f:=Nat.cast_nonneg _
    linarith
  have hU:((Q.extendedIndices 1).card:ℝ)≤εabs*Fintype.card V+f:=by
    have hh:=hcap.2.1
    rw [hJ0,hcard0] at hh
    have hf:(0:ℝ)≤f:=Nat.cast_nonneg _
    linarith
  have hterm:(Q.extendedVertices (L+1)).card+(Q.extendedIndices (L+1)).card≤size:=by
    have hh:=hcap.2.2
    simp only [Function.Embedding.coe_refl,Finset.image_id] at hh
    rw [hIL,hJL] at hh
    exact hh.trans hsize
  exact ⟨hterm,hV,hU⟩
end Oberwolfach
