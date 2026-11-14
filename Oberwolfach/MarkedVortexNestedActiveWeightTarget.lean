module

public import Oberwolfach.MarkedVortexNestedActiveWeightRecordInput
public import Oberwolfach.MarkedVortexActiveHubCardinality

@[expose] public section
/-! The original active weight satisfies the nested record condition with
the hub count in the nested parent representation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_nested_active_weight_target
    (π:Equiv.Perm V) (hπ:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (i d c:ℕ) (rho τ aLo B:ℝ)
    (weight:(Fin (c+1)→↥((Finset.univ\markedVortexInnerVertices Q (i+1)):
      Finset (markedVortexVertexType Q (i+1))))→ℝ)
    (hw:SuccessorSequenceWeightConditions (G.comap (markedVortexActiveVertexEmbedding Q (i+1)))
      (markedVortexActivePermutation Q π hπ (i+1)) (3*d)
      (2*((((Finset.univ\markedVortexInnerHubs Q (i+1)):
        Finset (markedVortexHubType Q (i+1))).card):ℝ)/rho) τ aLo B weight):
    let fP:=markedVortexVertexEmbedding Q i
    let fA:=markedVortexNonDeeperVertexEmbedding Q i
    let f:=markedVortexNextActiveInNonDeeper Q i
    let ρ:=markedVortexActivePermutation Q π hπ (i+1);
    SuccessorSequenceWeightConditions (((G.comap fP).comap fA).comap f) ρ (3*d)
      (2*((markedVortexInnerNonDeeperHubs Q i).card:ℝ)/rho) τ aLo B weight:=by
  intro fP fA f ρ
  have hh:=marked_vortex_nested_active_weight_record_input Q π hπ i d c _ τ aLo B weight hw
  rw [marked_vortex_active_hub_degree_target Q i rho] at hh
  exact hh
end Oberwolfach
