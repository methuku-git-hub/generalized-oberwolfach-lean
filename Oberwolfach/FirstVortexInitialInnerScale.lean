module

public import Oberwolfach.FirstVortexHostScaleToInner
public import Oberwolfach.MarkedFixedVortexSizes
public import Oberwolfach.MarkedInitialInnerVertexBound

@[expose] public section
/-! The first protected domain has the scale required by the initial level
record, and its ambient-size upper bound holds for the same vortex. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_initial_inner_scale
    {n D m:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (G:SimpleGraph (Fin n)) (β ε:ℝ) (Q:Vortex U G D β ε m)
    (hε:0<ε) (hm:0<m):
    let W:=markedVortexVertexType Q 0
    let I:=markedVortexInnerVertices Q 0;
    (ε/4)*Fintype.card W≤(I.card:ℝ) ∧ (I.card:ℝ)≤ε*n :=by
  intro W I
  have hW:Fintype.card W=n:=by
    change Fintype.card (Q.extendedVertices 0)=n
    rw [Fintype.card_coe,Q.extendedVertices_eq (Nat.zero_le Q.length),Q.initial,Finset.card_univ,Fintype.card_fin]
  have hI:I.card=(Q.extendedVertices 1).card:=by
    dsimp only [I]
    simpa only [Nat.zero_add] using (marked_vortex_inner_cardinalities Q 0).1
  have hp:=vortex_first_inner_positive_from_terminal Q hε hm
  have hlo:ε*(n:ℝ)/2≤(Q.extendedVertices 1).card:=by
    simpa only [Fintype.card_fin] using Q.first_inner_vertex_size_lower hε hp
  have hhi:((Q.extendedVertices 1).card:ℝ)≤ε*n:=by
    simpa only [Fintype.card_fin] using marked_initial_inner_vertex_bound Q hε.le
  rw [hW,hI]
  constructor <;> nlinarith [mul_nonneg hε.le (Nat.cast_nonneg n)]
end Oberwolfach
