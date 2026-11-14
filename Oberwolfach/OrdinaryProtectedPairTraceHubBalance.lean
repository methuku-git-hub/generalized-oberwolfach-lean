module

public import Oberwolfach.OrdinaryUniformInnerHubEvent
public import Oberwolfach.OrdinaryProtectedTraceHostLe
public import Oberwolfach.OrdinaryVortexTraceLocalExactBalance

@[expose] public section
/-! At an actual protected trace, local reference agreement supplies conflict
freedom while the same sampled event supplies the adaptive hub weights. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_protected_pair_trace_hub_balance
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U]
    (mWheel:ℕ) (P Gbase:SimpleGraph V) (Hbase:V→U→Prop) (D mv:ℕ) (β ε:ℝ)
    (Q:Vortex U P D β ε mv) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d:ℕ) (s:U→Color→ℝ) (j:Color) (σ:RawWheelOutcome V U Γ Color)
    (K:Finset (Sym2 V⊕(V×U))) (Inner:Finset V)
    (hInner:Q.extendedVertices 1⊆Inner) (hGbase:Gbase≤P)
    (hr:∀v∈Inner,∀w∈Inner,
      ((rawWheelGraph P σ)\permutationConflictGraph π (3*d)).Adj v w↔Gbase.Adj v w)
    (pR pH density εR εH βe βh bHub BHub ηHub capHub:ℝ)
    (hfamily:OrdinaryUniformInnerHubEvent mWheel P D mv d β ε Q π hπ pR pH βe βh bHub BHub ηHub capHub
      (fun _=>density) (fun k=>εR*(markedVortexInnerVertices Q k).card)
      (fun k=>εH*(markedVortexInnerHubs Q k).card) s j σ)
    (cost deepCost:ℕ→ℝ) (i:ℕ) (hi:i+1<Q.length)
    (A:Finset (Sym2 V⊕(V×U))) (G:SimpleGraph V) (Hs:V→U→Prop) (Ledit:ℝ)
    (hL:0≤Ledit) (hcap:Ledit≤capHub*(markedVortexInnerVertices Q (i+1)).card):
    let F:=permutationConflictGraph π (3*d);let S:=Gbase\ordinaryResourceRim Gbase K;
    let H:=fun v u=>Hbase v u∧¬(Sum.inr (v,u)∈K);
    let X:=fun k=>Q.extendedVertices (k+1);let T:=fun k=>Q.extendedVertices (k+2);
    let Z:=fun k=>Q.extendedIndices (k+1);let W:=fun k=>Q.extendedIndices (k+2);
    let f:=markedVortexVertexEmbedding Q (i+1);let g:=markedVortexHubEmbedding Q (i+1);
    let I:=markedVortexInnerVertices Q (i+1);let B:=markedVortexInnerHubs Q (i+1);
    let ρ:=markedVortexPermutation Q π hπ (i+1);let raw:=ordinaryRawRestrictPair f g σ;
    OrdinaryProtectedTrace S H X T Z W cost deepCost (i+1) A → ordinaryHostResources G Hs=A→
    (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
    (∀u,(mWheel+1)∣(Finset.univ.filter (fun v=>Hs v u)).card)→
    OrdinaryCleanupParentProfiles (P.comap f) (G.comap f) (F.comap f) (fun v u=>Hs (f v) (g u))
      ρ d I B pR pH density (εR*I.card) (εH*B.card) Ledit βe βh (fun u=>s (g u)) j raw→
    (G.comap f)≤(P.comap f)\(F.comap f) ∧
    OrdinaryAdaptiveHubWeightsInnerScaleLevelEvent mWheel (P.comap f) (F.comap f) I B ρ d pR pH density
      (εR*I.card) (εH*B.card) Ledit βe βh bHub BHub ηHub (fun u=>s (g u)) j raw ∧
    Nonempty (OrdinaryMixedHubWeightsInnerScale mWheel bHub BHub ηHub (G.comap f) (F.comap f)
      (fun v u=>Hs (f v) (g u)) I B) ∧
    (∀v,(G.comap f).degree v=2*(Finset.univ.filter (fun u=>Hs (f v) (g u))).card) ∧
    (∀u,(mWheel+1)∣(Finset.univ.filter (fun v=>Hs (f v) (g u))).card) :=by
  intro F S H X T Z W f g I B ρ raw htrace hstate hbal hdiv profile
  have hGle:G≤Gbase:=
    (ordinary_protected_trace_host_le S G H Hs X T Z W cost deepCost (i+1) A htrace hstate).trans sdiff_le
  have hsub:(G.comap f)≤(P.comap f)\(F.comap f):=by
    intro v w hvw
    have hv:(f v)∈Inner:=hInner ((Q.extendedVertices_subset (by omega : 1 ≤ i+1)) v.property)
    have hw:(f w)∈Inner:=hInner ((Q.extendedVertices_subset (by omega : 1 ≤ i+1)) w.property)
    have hfrom:((rawWheelGraph P σ)\F).Adj (f v) (f w):=(hr (f v) hv (f w) hw).mpr (hGle hvw)
    exact ⟨hGbase (hGle hvw),hfrom.2⟩
  have hevent:=hfamily (i+1) hi Ledit hL hcap
  have hhub:=hevent (G.comap f) (fun v u=>Hs (f v) (g u))
    (by convert profile using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _) (hsub.trans sdiff_le)
  have hexact:=ordinary_vortex_trace_local_exact_balance P S G H Hs D mv β ε Q (mWheel+1) i cost deepCost A
    htrace hstate hbal hdiv
  refine ⟨hsub,?_,?_,?_,?_⟩
  · convert hevent using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  · convert hhub using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  · convert hexact.1 using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  · convert hexact.2 using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
end Oberwolfach
