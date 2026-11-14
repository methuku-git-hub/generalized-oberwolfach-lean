module

public import Oberwolfach.OrdinaryTraceRawPairRestrictedEdits
public import Oberwolfach.OrdinaryRawPairRestrictionComposition
public import Oberwolfach.OrdinaryNondeeperIntoParent
public import Oberwolfach.OrdinaryVortexCorrectionConflictEdits
public import Oberwolfach.OrdinaryVortexProtectedNesting

@[expose] public section
/-! The actual later vortex trace has the same-sample nondeeper edit bounds;
the only initial local loss is the bounded permutation-conflict degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_vortex_trace_nondeeper_edits
    (P JQ:SimpleGraph V) (JH:V→U→Prop) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U P D β ε m) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d:ℕ) (j:Color) (σ:RawWheelOutcome V U Γ Color)
    (K:Finset (Sym2 V⊕(V×U)))
    (hJQ:∀v∈Q.extendedVertices 1,∀w∈Q.extendedVertices 1,¬JQ.Adj v w)
    (hJH:∀v u,JH v u→¬(v∈Q.extendedVertices 1 ∧ u∈Q.extendedIndices 1))
    (havoid:Disjoint K (ordinaryRootResources (Q.extendedVertices 1) (Q.extendedIndices 1)))
    (cost deepCost:ℕ→ℝ) (i:ℕ) (A:Finset (Sym2 V⊕(V×U))) (G:SimpleGraph V) (Hs:V→U→Prop)
    (ρ₂:Equiv.Perm (ordinaryVortexNondeeperVertexType Q (i+1)))
    (hcomm₂:∀x,(ρ₂ x).val=π x.val):
    let F:=permutationConflictGraph π (3*d)
    let R:=rawWheelGraph P σ;let J:=rawWheelSpokes π d σ j
    let S:=(R\F)\JQ;let H:=fun v u=>J v u∧¬JH v u
    let S₀:=S\ordinaryResourceRim S K;let H₀:=fun v u=>H v u∧¬(Sum.inr (v,u)∈K)
    let X:=fun k=>Q.extendedVertices (k+1);let T:=fun k=>Q.extendedVertices (k+2)
    let Z:=fun k=>Q.extendedIndices (k+1);let W:=fun k=>Q.extendedIndices (k+2);
    OrdinaryProtectedTrace S₀ H₀ X T Z W cost deepCost (i+1) A → ordinaryHostResources G Hs=A →
    let f₁:markedVortexVertexType Q (i+1)↪V:=(markedVortexVertexEmbedding Q (i+1)).toEmbedding
    let g₁:markedVortexHubType Q (i+1)↪U:=markedVortexHubEmbedding Q (i+1)
    let f₂:=ordinaryNondeeperVertexToParent Q (i+1)
    let g₂:=ordinaryNondeeperHubToParent Q (i+1)
    let raw:=ordinaryRawRestrictPair f₂ g₂ (ordinaryRawRestrictPair f₁ g₁ σ)
    let P₂:=(P.induce ((X i):Set V)).comap f₂
    let G₂:=(G.induce ((X i):Set V)).comap f₂
    let Hlocal:=fun v u=>Hs (f₁ (f₂ v)) (g₁ (g₂ u));
    (∀v,((changed ((rawWheelGraph P₂ raw).neighborFinset v) (G₂.neighborFinset v)).card:ℝ)≤2*((3*d:ℕ):ℝ)+cost i) ∧
    (∀v,((changed (Finset.univ.filter (rawWheelSpokes ρ₂ d raw j v)) (Finset.univ.filter (Hlocal v))).card:ℝ)≤2*((3*d:ℕ):ℝ)+cost i) ∧
    (∀u,((changed (Finset.univ.filter (fun v=>rawWheelSpokes ρ₂ d raw j v u)) (Finset.univ.filter (fun v=>Hlocal v u))).card:ℝ)≤2*((3*d:ℕ):ℝ)+cost i) :=by
  intro F R J S H S₀ H₀ X T Z W htrace hstate f₁ g₁ f₂ g₂ raw P₂ G₂ Hlocal
  let ρ:=markedVortexPermutation Q π hπ (i+1)
  have hc:∀x:markedVortexVertexType Q (i+1),(ρ x).val=π x.val:=fun _=>rfl
  have hc₂:∀x,f₂ (ρ₂ x)=ρ (f₂ x):=by
    intro x
    apply Subtype.ext
    exact hcomm₂ x
  have hbase:=ordinary_vortex_correction_conflict_edits P R JQ D m β ε Q J JH K π (3*d) hJQ hJH havoid i
  have hnest:=ordinary_vortex_protected_nesting P D m β ε Q i
  have hlocal:=ordinary_trace_raw_pair_restricted_edits P S₀ H₀ π d j σ X T Z W cost deepCost i A G Hs
    ρ hc (2*((3*d:ℕ):ℝ)) hbase htrace hstate hnest.1 hnest.2 f₂ g₂ ρ₂ hc₂
  convert hlocal using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
