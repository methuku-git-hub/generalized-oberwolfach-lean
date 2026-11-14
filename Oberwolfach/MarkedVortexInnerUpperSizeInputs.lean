module

public import Oberwolfach.MarkedFixedVortexSizes

@[expose] public section
/-! The independently rounded inner sets are small relative to the parent
vertex type when the vortex ratio is below the record tolerance. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_inner_upper_size_inputs
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V) (hD:0<D)
    (hρhi:initialIndexDensity U D≤1) (he:0≤ε) (ξ:ℝ) (heξ:ε≤ξ)
    (L:ℕ) (hL:L<Q.length):
    ∀ i≤L,
      let W:=markedVortexVertexType Q i
      let I:=markedVortexInnerVertices Q i
      let J:=markedVortexInnerHubs Q i
      (I.card:ℝ)≤ξ*Fintype.card W ∧ (J.card:ℝ)≤ξ*Fintype.card W:=by
  intro i hi W I J
  have hcard:Fintype.card (markedVortexHubType Q i)≤Fintype.card W:=by
    have hh:=Q.index_size_upper hreg hn hD he hρhi (i:=i) (by omega)
    change Fintype.card ↥(Q.extendedIndices i)≤Fintype.card ↥(Q.extendedVertices i)
    simp only [Fintype.card_coe]
    rw [Q.extendedIndices_eq (by omega:i≤Q.length),Q.extendedVertices_eq (by omega:i≤Q.length)]
    omega
  have hW:Fintype.card W=(Q.extendedVertices i).card:=by
    change Fintype.card ↥(Q.extendedVertices i)=(Q.extendedVertices i).card
    simp only [Fintype.card_coe]
  have hZ:Fintype.card (markedVortexHubType Q i)=(Q.extendedIndices i).card:=by
    change Fintype.card ↥(Q.extendedIndices i)=(Q.extendedIndices i).card
    simp only [Fintype.card_coe]
  obtain ⟨hI,_,hJ,_⟩:=marked_vortex_inner_cardinalities Q i
  have hstep:=Q.extended_successor_size_bounds he i
  have hW0:(0:ℝ)≤Fintype.card W:=Nat.cast_nonneg _
  have hZle:(Fintype.card (markedVortexHubType Q i):ℝ)≤Fintype.card W:=by exact_mod_cast hcard
  have hIl:(I.card:ℝ)≤ε*Fintype.card W:=by rw [hI,hW];exact hstep.1
  have hJl:(J.card:ℝ)≤ε*Fintype.card W:=by
    have hJ0:(J.card:ℝ)≤ε*Fintype.card (markedVortexHubType Q i):=by rw [hJ,hZ];exact hstep.2
    exact hJ0.trans (mul_le_mul_of_nonneg_left hZle he)
  exact ⟨hIl.trans (mul_le_mul_of_nonneg_right heξ hW0),hJl.trans (mul_le_mul_of_nonneg_right heξ hW0)⟩
end Oberwolfach
