module

public import Oberwolfach.OrdinaryInnerBalanceInducedTransport
public import Oberwolfach.MarkedFixedVortexGeometry

@[expose] public section
/-! The actual ambient vortex-pair balance transfers to the local inner
pair used by the ordinary wheel correction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_vortex_inner_balance_induced_transport
    (P G:SimpleGraph V) (H:V→U→Prop) (D m:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε m) (i:ℕ) (b:ℝ)
    (hbal:∀v∈Q.extendedVertices (i+2),|((spanningRestriction G (Q.extendedVertices (i+2))).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H v u∧v∈Q.extendedVertices (i+2)∧u∈Q.extendedIndices (i+2))).card|≤b):
    let f:=markedVortexVertexEmbedding Q (i+1);let g:=markedVortexHubEmbedding Q (i+1);
    let I:=markedVortexInnerVertices Q (i+1);let J:=markedVortexInnerHubs Q (i+1);
    ∀v:I,|(((G.comap f).induce (I:Set _)).degree v:ℝ)-
      2*(Finset.univ.filter (fun u:J=>H (f v.val) (g u.val))).card|≤b :=by
  intro f g I J v
  have hI:Q.extendedVertices (i+2)⊆Q.extendedVertices (i+1):=Q.extendedVertices_subset (by omega)
  have hJ:Q.extendedIndices (i+2)⊆Q.extendedIndices (i+1):=Q.extendedIndices_subset (by omega)
  have hh:=ordinary_inner_balance_induced_transport G H (Q.extendedVertices (i+1)) (Q.extendedVertices (i+2))
    (Q.extendedIndices (i+1)) (Q.extendedIndices (i+2)) hI hJ b hbal
  have hv:=hh v
  convert hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
