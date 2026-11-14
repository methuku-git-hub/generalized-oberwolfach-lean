module

public import Oberwolfach.OrdinaryVortexCorrectionConflictEdits
public import Oberwolfach.OrdinaryRawPairStateEquality
public import Oberwolfach.MarkedFixedVortexGeometry

@[expose] public section
/-! On every later parent, the initial protected correction and absorber
change the raw sample only through the bounded conflict graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_vortex_initial_protected_physical_edit
    (P JQ:SimpleGraph V) (JH:V→U→Prop) (D m:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε m)
    (π:Equiv.Perm V) (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d:ℕ) (j:Color) (σ:RawWheelOutcome V U Γ Color) (K:Finset (Sym2 V⊕(V×U)))
    (hJQ:∀v∈Q.extendedVertices 1,∀w∈Q.extendedVertices 1,¬JQ.Adj v w)
    (hJH:∀v u,JH v u→¬(v∈Q.extendedVertices 1 ∧ u∈Q.extendedIndices 1))
    (havoid:Disjoint K (ordinaryRootResources (Q.extendedVertices 1) (Q.extendedIndices 1)))
    (i:ℕ):
    let f:markedVortexVertexType Q (i+1)↪V:=(markedVortexVertexEmbedding Q (i+1)).toEmbedding;let g:=markedVortexHubEmbedding Q (i+1);
    let ρ:=markedVortexPermutation Q π hπ (i+1);let raw:=ordinaryRawRestrictPair f g σ;
    let F:=permutationConflictGraph π (3*d);let R:=rawWheelGraph P σ;let J:=rawWheelSpokes π d σ j;
    let S:=(R\F)\JQ;let H:=fun v u=>J v u∧¬JH v u;
    let S₀:=S\ordinaryResourceRim S K;let H₀:=fun v u=>H v u∧¬(Sum.inr (v,u)∈K);
    ∀w:markedVortexVertexType Q (i+1)⊕markedVortexHubType Q (i+1),
      ((changed ((ordinaryPhysicalGraph (rawWheelGraph (P.comap f) raw) (rawWheelSpokes ρ d raw j)).neighborFinset w)
        ((ordinaryPhysicalGraph (S₀.comap f) (fun v u=>H₀ (f v) (g u))).neighborFinset w)).card:ℝ)≤2*((3*d:ℕ):ℝ) :=by
  intro f g ρ raw F R J S H S₀ H₀
  have hbase:=ordinary_vortex_correction_conflict_edits P R JQ D m β ε Q J JH K π (3*d) hJQ hJH havoid i
  have hgraph:rawWheelGraph (P.comap f) raw=R.induce ((Q.extendedVertices (i+1)):Set V):=
    ordinary_raw_pair_graph_eq f g P σ
  have hcomm:∀x,f (ρ x)=π (f x):=(marked_vortex_permutation_compatibility Q π hπ (i+1)).1
  have hspoke:rawWheelSpokes ρ d raw j=fun v u=>J (f v) (g u):=by
    convert ordinary_raw_pair_spokes_eq f g π ρ hcomm d σ j using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  intro w
  rw [hgraph,hspoke]
  convert hbase w using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
