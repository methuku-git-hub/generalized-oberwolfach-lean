module

public import Oberwolfach.OrdinaryVortexTraceNondeeperEdits
public import Oberwolfach.OrdinaryTypedChangesTransport
public import Oberwolfach.OrdinaryNondeeperNestedSampleIdentification
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

theorem ordinary_vortex_trace_nondeeper_direct_edits
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
    let f:=ordinaryVortexNondeeperVertexEmbedding Q (i+1)
    let g:=ordinaryVortexNondeeperHubEmbedding Q (i+1)
    let raw:=ordinaryRawRestrictPair f g σ
    let Hlocal:=fun v u=>Hs (f v) (g u);
    (∀v,((changed ((rawWheelGraph (P.comap f) raw).neighborFinset v) ((G.comap f).neighborFinset v)).card:ℝ)≤2*((3*d:ℕ):ℝ)+cost i) ∧
    (∀v,((changed (Finset.univ.filter (rawWheelSpokes ρ₂ d raw j v)) (Finset.univ.filter (Hlocal v))).card:ℝ)≤2*((3*d:ℕ):ℝ)+cost i) ∧
    (∀u,((changed (Finset.univ.filter (fun v=>rawWheelSpokes ρ₂ d raw j v u)) (Finset.univ.filter (fun v=>Hlocal v u))).card:ℝ)≤2*((3*d:ℕ):ℝ)+cost i) :=by
  intro F R J S H S₀ H₀ X T Z W htrace hstate f g raw Hlocal
  let f₁:markedVortexVertexType Q (i+1)↪V:=(markedVortexVertexEmbedding Q (i+1)).toEmbedding
  let g₁:markedVortexHubType Q (i+1)↪U:=markedVortexHubEmbedding Q (i+1)
  let f₂:=ordinaryNondeeperVertexToParent Q (i+1)
  let g₂:=ordinaryNondeeperHubToParent Q (i+1)
  let raw₂:=ordinaryRawRestrictPair f₂ g₂ (ordinaryRawRestrictPair f₁ g₁ σ)
  let P₂:=(P.induce ((X i):Set V)).comap f₂
  let G₂:=(G.induce ((X i):Set V)).comap f₂
  let H₂:=fun v u=>Hs (f₁ (f₂ v)) (g₁ (g₂ u))
  have hlocal:=ordinary_vortex_trace_nondeeper_edits P JQ JH D m β ε Q π hπ d j σ K hJQ hJH havoid
    cost deepCost i A G Hs ρ₂ hcomm₂ htrace hstate
  have hraw:raw₂=raw:=by
    dsimp only [raw₂,raw,f,g]
    rw [ordinary_raw_pair_restriction_comp,ordinary_nondeeper_vertex_embedding_composition,
      ordinary_nondeeper_hub_embedding_composition]
  have hP:P₂=P.comap f:=by ext x y;rfl
  have hG:G₂=G.comap f:=by ext x y;rfl
  have hH:H₂=Hlocal:=by rfl
  have hGraph:rawWheelGraph P₂ raw₂=rawWheelGraph (P.comap f) raw:=
    (congrArg (fun T=>rawWheelGraph T raw₂) hP).trans (congrArg (fun t=>rawWheelGraph (P.comap f) t) hraw)
  have hSpoke:rawWheelSpokes ρ₂ d raw₂ j=rawWheelSpokes ρ₂ d raw j:=
    congrArg (fun t=>rawWheelSpokes ρ₂ d t j) hraw
  apply ordinary_typed_changes_transport (rawWheelGraph P₂ raw₂) G₂ (rawWheelGraph (P.comap f) raw) (G.comap f)
    (rawWheelSpokes ρ₂ d raw₂ j) H₂ (rawWheelSpokes ρ₂ d raw j) Hlocal (2*((3*d:ℕ):ℝ)+cost i)
    hGraph hG hSpoke hH
  convert hlocal using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
