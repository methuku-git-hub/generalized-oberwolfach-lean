module

public import Oberwolfach.OrdinaryAdaptiveHubWeightsInnerScaleLevelEvent
public import Oberwolfach.OrdinaryVortexTraceFullParentHost

@[expose] public section
/-! The all-level inner hub-weight event applies to the actual edited host
of a protected trace, with the same raw sample and its actual edit budget. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_trace_inner_hub_from_uniform
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U]
    (P JQ:SimpleGraph V) (JH:V→U→Prop) (D mv:ℕ) (β ε:ℝ)
    (Q:Vortex U P D β ε mv) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d:ℕ) (s:U→Color→ℝ) (j:Color) (σ:RawWheelOutcome V U Γ Color)
    (pR pH density εR εH eParent hParent b B η cap:ℝ)
    (K:Finset (Sym2 V⊕(V×U))) (cost deepCost:ℕ→ℝ) (i:ℕ) (hi:i+1<Q.length)
    (A:Finset (Sym2 V⊕(V×U))) (G:SimpleGraph V) (Hs:V→U→Prop):
    let F:=permutationConflictGraph π (3*d);let R:=rawWheelGraph P σ;let J:=rawWheelSpokes π d σ j;
    let S:=(R\F)\JQ;let H:=fun v u=>J v u∧¬JH v u;
    let S₀:=S\ordinaryResourceRim S K;let H₀:=fun v u=>H v u∧¬(Sum.inr (v,u)∈K);
    let X:=fun k=>Q.extendedVertices (k+1);let T:=fun k=>Q.extendedVertices (k+2);
    let Z:=fun k=>Q.extendedIndices (k+1);let W:=fun k=>Q.extendedIndices (k+2);
    let f:=markedVortexVertexEmbedding Q (i+1);let g:=markedVortexHubEmbedding Q (i+1);
    let I:=markedVortexInnerVertices Q (i+1);let Bset:=markedVortexInnerHubs Q (i+1);
    let ρi:=markedVortexPermutation Q π hπ (i+1);let Ploc:=P.comap f;let Floc:=F.comap f;
    let Gloc:=G.comap f;let Hloc:=fun v u=>Hs (f v) (g u);let raw:=ordinaryRawRestrictPair f g σ;
    OrdinaryProtectedTrace S₀ H₀ X T Z W cost deepCost (i+1) A→ ordinaryHostResources G Hs=A→
    (∀Lold:ℝ,0≤Lold→Lold≤cap*I.card→
      OrdinaryAdaptiveHubWeightsInnerScaleLevelEvent 2 Ploc Floc I Bset ρi d pR pH density
        (εR*I.card) (εH*Bset.card) Lold (eParent*ε) (hParent*ε) b B η (fun u=>s (g u)) j raw)→
    ∀Ledit:ℝ,0≤Ledit→Ledit≤cap*I.card→
    OrdinaryCleanupParentProfiles Ploc Gloc Floc Hloc ρi d I Bset pR pH density
      (εR*I.card) (εH*Bset.card) Ledit (eParent*ε) (hParent*ε) (fun u=>s (g u)) j raw→
    Nonempty (OrdinaryMixedHubWeightsInnerScale 2 b B η Gloc Floc Hloc I Bset):=by
  intro F R J S H S₀ H₀ X T Z W f g I Bset ρi Ploc Floc Gloc Hloc raw htrace hstate hfamily Ledit hL hcap profile
  have hsub:Gloc≤Ploc\Floc:=ordinary_vortex_trace_full_parent_host_subgraph
    P JQ JH D mv β ε Q π d j σ K cost deepCost i A G Hs htrace hstate
  have hw:=hfamily Ledit hL hcap Gloc Hloc
    (by convert profile using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _) (hsub.trans sdiff_le)
  convert hw using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
end Oberwolfach
