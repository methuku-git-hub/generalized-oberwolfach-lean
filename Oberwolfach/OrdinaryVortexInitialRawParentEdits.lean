module

public import Oberwolfach.OrdinaryVortexCorrectionConflictEdits
public import Oberwolfach.OrdinaryRawPairStateEquality
public import Oberwolfach.HubToRowDeletion
public import Oberwolfach.MarkedFixedVortexGeometry

@[expose] public section
/-! The protected correction changes each later parent only by the fixed
conflict-degree allowance, before any level deletion is applied. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_vortex_initial_raw_parent_edits
    (P JQ:SimpleGraph V) (JH:V→U→Prop) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U P D β ε m) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d:ℕ) (j:Color) (σ:RawWheelOutcome V U Γ Color) (K:Finset (Sym2 V⊕(V×U)))
    (hJQ:∀v∈Q.extendedVertices 1,∀w∈Q.extendedVertices 1,¬JQ.Adj v w)
    (hJH:∀v u,JH v u→¬(v∈Q.extendedVertices 1 ∧ u∈Q.extendedIndices 1))
    (havoid:Disjoint K (ordinaryRootResources (Q.extendedVertices 1) (Q.extendedIndices 1)))
    (i:ℕ):
    let F:=permutationConflictGraph π (3*d)
    let R:=rawWheelGraph P σ;let J:=rawWheelSpokes π d σ j
    let S:=(R\F)\JQ;let H:=fun v u=>J v u∧¬JH v u
    let S₀:=S\ordinaryResourceRim S K;let H₀:=fun v u=>H v u∧¬(Sum.inr (v,u)∈K)
    let f:=markedVortexVertexEmbedding Q (i+1);let g:=markedVortexHubEmbedding Q (i+1)
    let ρ:=markedVortexPermutation Q π hπ (i+1);let raw:=ordinaryRawRestrictPair f g σ
    let Hlocal:=fun v u=>H₀ (f v) (g u);
    (∀v,((changed ((rawWheelGraph (P.comap f) raw).neighborFinset v) ((S₀.comap f).neighborFinset v)).card:ℝ)≤2*((3*d:ℕ):ℝ)) ∧
    (∀v,((changed (Finset.univ.filter (rawWheelSpokes ρ d raw j v)) (Finset.univ.filter (Hlocal v))).card:ℝ)≤2*((3*d:ℕ):ℝ)):=by
  intro F R J S H S₀ H₀ f g ρ raw Hlocal
  have hbase:=ordinary_vortex_correction_conflict_edits P R JQ D m β ε Q J JH K π (3*d) hJQ hJH havoid i
  have htyped:=ordinary_physical_edit_to_typed_changes
    (R.induce ((Q.extendedVertices (i+1)):Set V)) (S₀.induce ((Q.extendedVertices (i+1)):Set V))
    (fun (v:↥(Q.extendedVertices (i+1))) (u:↥(Q.extendedIndices (i+1)))=>J v.val u.val)
    (fun (v:↥(Q.extendedVertices (i+1))) (u:↥(Q.extendedIndices (i+1)))=>H₀ v.val u.val)
    (2*((3*d:ℕ):ℝ)) hbase
  have hr:rawWheelGraph (P.comap f) raw=R.induce ((Q.extendedVertices (i+1)):Set V):=by
    exact ordinary_raw_pair_graph_eq f.toEmbedding g P σ
  have hs:rawWheelSpokes ρ d raw j=fun (v:markedVortexVertexType Q (i+1)) (u:markedVortexHubType Q (i+1))=>J v.val u.val:=by
    convert ordinary_raw_pair_spokes_eq f.toEmbedding g π ρ (by intro x;rfl) d σ j using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  constructor
  · intro v
    rw [hr]
    convert htyped.1 v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro v
    rw [hs]
    convert htyped.2.1 v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
