module

public import Oberwolfach.MarkedFixedVortexGeometry
public import Oberwolfach.OrdinaryInnerBalanceInducedReverse
public import Oberwolfach.OrdinaryCrossBalanceInducedReverse

@[expose] public section
/-! Transfer both local balance bounds to their ambient vortex sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 26000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_vortex_local_balance_to_ambient
    (P G:SimpleGraph V) (H:V→U→Prop) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U P D β ε m) (i:ℕ) (b:ℝ)
    (hinner: let f:=markedVortexVertexEmbedding Q i;let g:=markedVortexHubEmbedding Q i;
      let I:=markedVortexInnerVertices Q i;let B:=markedVortexInnerHubs Q i;
      ∀v:I,|(((G.comap f).induce (I:Set _)).degree v:ℝ)-
        2*(Finset.univ.filter (fun u:B=>H (f v.val) (g u.val))).card|≤b)
    (hcross: let f:=markedVortexVertexEmbedding Q i;let g:=markedVortexHubEmbedding Q i;
      let I:=markedVortexInnerVertices Q i;let B:=markedVortexInnerHubs Q i;
      ∀v∉I,|(((G.comap f).neighborFinset v∩I).card:ℝ)-2*(B.filter (fun u=>H (f v) (g u))).card|≤b):
    (∀v∈Q.extendedVertices (i+1),|((spanningRestriction G (Q.extendedVertices (i+1))).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H v u∧v∈Q.extendedVertices (i+1)∧u∈Q.extendedIndices (i+1))).card|≤b) ∧
    (∀v∈Q.extendedVertices i,v∉Q.extendedVertices (i+1)→
      |((G.neighborFinset v∩Q.extendedVertices (i+1)).card:ℝ)-
        2*((Q.extendedIndices (i+1)).filter (H v)).card|≤b) :=by
  have hI:Q.extendedVertices (i+1)⊆Q.extendedVertices i:=Q.extendedVertices_subset (by omega)
  have hJ:Q.extendedIndices (i+1)⊆Q.extendedIndices i:=Q.extendedIndices_subset (by omega)
  have hf : (markedVortexVertexEmbedding Q i : markedVortexVertexType Q i → V) = Subtype.val := rfl
  have hg : (markedVortexHubEmbedding Q i : markedVortexHubType Q i → U) = Subtype.val := rfl
  dsimp only at hinner hcross
  have hG : G.comap (markedVortexVertexEmbedding Q i) = G.induce (Q.extendedVertices i : Set V) := by
    ext x y
    rfl
  simp only [hG,hf,hg] at hinner hcross
  constructor
  · apply ordinary_inner_balance_induced_reverse G H (Q.extendedVertices i) (Q.extendedVertices (i+1))
      (Q.extendedIndices i) (Q.extendedIndices (i+1)) hI hJ b
    simp only [markedVortexInnerVertices,markedVortexInnerHubs] at hinner ⊢
    convert hinner using 1 <;> congr! 8 <;> try (apply Finset.ext; intro x; simp) <;> try rfl
  · apply ordinary_cross_balance_induced_reverse G H (Q.extendedVertices i) (Q.extendedVertices (i+1))
      (Q.extendedIndices i) (Q.extendedIndices (i+1)) hI hJ b
    simp only [markedVortexInnerVertices,markedVortexInnerHubs] at hcross ⊢
    convert hcross using 1 <;> congr! 8 <;> try (apply Finset.ext; intro x; simp) <;> try rfl
end Oberwolfach
