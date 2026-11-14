module

public import Oberwolfach.MarkedVortexNestedActiveRowsLoads
public import Oberwolfach.MarkedNestedVortexActiveWeights

@[expose] public section
/-! The fixed active weight family is used unchanged on the nested graph in
the level record, with its original active-hub degree target. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_nested_active_weight_record_input
    (π:Equiv.Perm V) (hπ:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (i d c:ℕ) (Dnext τ aLo B:ℝ)
    (weight:(Fin (c+1)→↥((Finset.univ\markedVortexInnerVertices Q (i+1)):
      Finset (markedVortexVertexType Q (i+1))))→ℝ)
    (hw:SuccessorSequenceWeightConditions (G.comap (markedVortexActiveVertexEmbedding Q (i+1)))
      (markedVortexActivePermutation Q π hπ (i+1)) (3*d) Dnext τ aLo B weight):
    let fP:=markedVortexVertexEmbedding Q i
    let fA:=markedVortexNonDeeperVertexEmbedding Q i
    let f:=markedVortexNextActiveInNonDeeper Q i
    let ρ:=markedVortexActivePermutation Q π hπ (i+1);
    SuccessorSequenceWeightConditions (((G.comap fP).comap fA).comap f) ρ (3*d) Dnext τ aLo B weight:=by
  intro fP fA f ρ
  exact hw
end Oberwolfach
