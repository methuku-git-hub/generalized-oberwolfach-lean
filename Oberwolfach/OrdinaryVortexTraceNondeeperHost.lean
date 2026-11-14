module

public import Oberwolfach.OrdinaryProtectedTraceHostLe
public import Oberwolfach.OrdinaryVortexNondeeperDomains
public import Oberwolfach.OrdinaryRawIntervalGeometry

@[expose] public section
/-! The actual protected trace remains in the host with conflict edges
removed, also after passing to a fixed nondeeper domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_vortex_trace_nondeeper_host_subgraph
    (P JQ:SimpleGraph V) (JH:V→U→Prop) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U P D β ε m) (π:Equiv.Perm V) (d:ℕ) (j:Color) (σ:RawWheelOutcome V U Γ Color)
    (K:Finset (Sym2 V⊕(V×U))) (cost deepCost:ℕ→ℝ) (i:ℕ)
    (A:Finset (Sym2 V⊕(V×U))) (G:SimpleGraph V) (Hs:V→U→Prop):
    let F:=permutationConflictGraph π (3*d)
    let R:=rawWheelGraph P σ;let J:=rawWheelSpokes π d σ j
    let S:=(R\F)\JQ;let H:=fun v u=>J v u∧¬JH v u
    let S₀:=S\ordinaryResourceRim S K;let H₀:=fun v u=>H v u∧¬(Sum.inr (v,u)∈K)
    let X:=fun k=>Q.extendedVertices (k+1);let T:=fun k=>Q.extendedVertices (k+2)
    let Z:=fun k=>Q.extendedIndices (k+1);let W:=fun k=>Q.extendedIndices (k+2);
    OrdinaryProtectedTrace S₀ H₀ X T Z W cost deepCost (i+1) A → ordinaryHostResources G Hs=A →
    G≤P\F ∧ (G.comap (ordinaryVortexNondeeperVertexEmbedding Q (i+1)))≤
      (P.comap (ordinaryVortexNondeeperVertexEmbedding Q (i+1)))\(F.comap (ordinaryVortexNondeeperVertexEmbedding Q (i+1))) :=by
  intro F R J S H S₀ H₀ X T Z W htrace hstate
  have hGS:=ordinary_protected_trace_host_le S₀ G H₀ Hs X T Z W cost deepCost (i+1) A htrace hstate
  have hRP:R≤P:=retainedGraph_le P (fun e=>σ (Sum.inl e))
  have hGF:G≤P\F:=by
    intro v w h
    have hh:=hGS h
    exact ⟨hRP hh.1.1.1,hh.1.1.2⟩
  refine ⟨hGF,?_⟩
  intro v w h
  exact hGF h
end Oberwolfach
