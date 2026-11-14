module

public import Oberwolfach.OrdinaryTraceRawPairWindowEditsLocal
public import Oberwolfach.OrdinaryVortexCorrectionConflictEdits
public import Oberwolfach.OrdinaryVortexBufferedNesting
public import Oberwolfach.MarkedFixedVortexGeometry

@[expose] public section
/-! The full current parent has the actual trace edit bounds on the original
sample; the protected correction adds only the conflict-degree term. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_vortex_trace_parent_buffered_direct_edits
    (P JQ:SimpleGraph V) (JH:V→U→Prop) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U P D β ε m) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d:ℕ) (j:Color) (σ:RawWheelOutcome V U Γ Color) (K:Finset (Sym2 V⊕(V×U)))
    (hJQ:∀v∈Q.extendedVertices 1,∀w∈Q.extendedVertices 1,¬JQ.Adj v w)
    (hJH:∀v u,JH v u→¬(v∈Q.extendedVertices 1 ∧ u∈Q.extendedIndices 1))
    (havoid:Disjoint K (ordinaryRootResources (Q.extendedVertices 1) (Q.extendedIndices 1)))
    (cost deepCost:ℕ→ℝ) (i buffer:ℕ) (hbuffer:2≤buffer) (A:Finset (Sym2 V⊕(V×U))) (G:SimpleGraph V) (Hs:V→U→Prop):
    let F:=permutationConflictGraph π (3*d)
    let R:=rawWheelGraph P σ;let J:=rawWheelSpokes π d σ j
    let S:=(R\F)\JQ;let H:=fun v u=>J v u∧¬JH v u
    let S₀:=S\ordinaryResourceRim S K;let H₀:=fun v u=>H v u∧¬(Sum.inr (v,u)∈K)
    let X:=fun k=>Q.extendedVertices (k+1);let T:=fun k=>Q.extendedVertices (k+buffer)
    let Z:=fun k=>Q.extendedIndices (k+1);let W:=fun k=>Q.extendedIndices (k+buffer);
    OrdinaryProtectedTrace S₀ H₀ X T Z W cost deepCost (i+1) A → ordinaryHostResources G Hs=A →
    let f:=markedVortexVertexEmbedding Q (i+1);let g:=markedVortexHubEmbedding Q (i+1)
    let ρ:=markedVortexPermutation Q π hπ (i+1);let raw:=ordinaryRawRestrictPair f g σ
    let Hlocal:=fun v u=>Hs (f v) (g u);
    let Jwin:=Finset.Icc (i+2-buffer) i;
    (∀v,((changed ((rawWheelGraph (P.comap f) raw).neighborFinset v) ((G.comap f).neighborFinset v)).card:ℝ)≤2*((3*d:ℕ):ℝ)+∑j∈Jwin,cost j) ∧
    (∀v,((changed (Finset.univ.filter (rawWheelSpokes ρ d raw j v)) (Finset.univ.filter (Hlocal v))).card:ℝ)≤2*((3*d:ℕ):ℝ)+∑j∈Jwin,cost j) ∧
    (∀u,((changed (Finset.univ.filter (fun v=>rawWheelSpokes ρ d raw j v u)) (Finset.univ.filter (fun v=>Hlocal v u))).card:ℝ)≤2*((3*d:ℕ):ℝ)+∑j∈Jwin,cost j) :=by
  intro F R J S H S₀ H₀ X T Z W htrace hstate f g ρ raw Hlocal Jwin
  have hbase:=ordinary_vortex_correction_conflict_edits P R JQ D m β ε Q J JH K π (3*d) hJQ hJH havoid i
  have hnest:=ordinary_vortex_buffered_nesting P D m β ε Q i buffer hbuffer
  have hh:=ordinary_trace_raw_pair_window_edits_local P S₀ H₀ π d j σ X T Z W cost deepCost i Jwin A G Hs
    ρ (by intro x;rfl) (2*((3*d:ℕ):ℝ)) hbase htrace hstate hnest.1 hnest.2.1 hnest.2.2.1 hnest.2.2.2.1 hnest.2.2.2.2
  convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
