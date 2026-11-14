module

public import Oberwolfach.OrdinaryVortexTraceProfileProtectedPair
public import Oberwolfach.OrdinaryProtectedPairTraceHubBalance
public import Oberwolfach.OrdinaryFixedVortexCleanupBalance
public import Oberwolfach.OrdinaryFixedVortexCleanupBothBalance
public import Oberwolfach.OrdinaryProtectedPairTracePhysicalEdit
public import Oberwolfach.OrdinaryFixedVortexCleanupInputs
public import Oberwolfach.OrdinaryVortexBufferedNesting

@[expose] public section
/-! The actual vortex supplies the nesting, local tests and parent degree
needed by the protected-trace cleanup profile at the next level. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_protected_pair_trace_sample_bundle
    (mWheel:ℕ) (P Gbase:SimpleGraph V) (Hbase:V→U→Prop) (D m:ℕ) (β ε θ α pR pH εR εH:ℝ)
    (Q:Vortex U P D β ε m) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d:ℕ) (s:U→Color→ℝ) (j:Color) (σ:RawWheelOutcome V U Γ Color)
    (K:Finset (Sym2 V⊕(V×U))) (Inner:Finset V) (Hubs:Finset U)
    (hInner:Q.extendedVertices 1⊆Inner) (hHubs:Q.extendedIndices 1⊆Hubs)
    (hr:∀v∈Inner,∀w∈Inner,((rawWheelGraph P σ)\permutationConflictGraph π (3*d)).Adj v w↔Gbase.Adj v w)
    (hsample:∀v∈Inner,∀u∈Hubs,rawWheelSpokes π d σ j v u↔Hbase v u)
    (hK:Disjoint K (ordinaryRootResources Inner Hubs))
    (LF:ℝ) (hLF:0≤LF) (hF:∀v,((permutationConflictGraph π (3*d)).degree v:ℝ)≤LF) (hGbase:Gbase≤P)
    (hn:0<Fintype.card V) (hreg:P.IsRegularOfDegree D)
    (hρ:0< initialIndexDensity U D) (hβ:0≤β) (hεR:0≤εR) (hεH:0≤εH) (hpR:0≤pR) (hpR1:pR≤1) (hpH:0≤pH)
    (hdensity:1/2≤θ+α-β/2) (hdegree:(θ+α)*Fintype.card V≤D)
    (hpEq:pR=initialIndexDensity U D*pH)
    (hs:∀u,s u j=pH)
    (hgood:OrdinaryFixedVortexRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d)) D m β ε Q π hπ pR pH s j σ)
    (cost deepCost:ℕ→ℝ) (i:ℕ) (hi:i+1<Q.length)
    (A:Finset (Sym2 V⊕(V×U))) (G:SimpleGraph V) (Hs:V→U→Prop)
    (βe βh bHub BHub ηHub capHub ηbalance:ℝ)
    (hfamily:OrdinaryUniformInnerHubEvent mWheel P D m d β ε Q π hπ pR pH βe βh bHub BHub ηHub capHub
      (fun _=>θ+α-β/2) (fun k=>εR*(markedVortexInnerVertices Q k).card)
      (fun k=>εH*(markedVortexInnerHubs Q k).card) s j σ)
    (hcost:∀k,0≤cost k)
    (hcap:LF+∑k∈Finset.Icc (i+2-2) i,cost k≤capHub*(markedVortexInnerVertices Q (i+1)).card):
    let F:=permutationConflictGraph π (3*d);
    let S:=Gbase\ordinaryResourceRim Gbase K;
    let H:=fun v u=>Hbase v u∧¬(Sum.inr (v,u)∈K);
    let X:=fun k=>Q.extendedVertices (k+1);let T:=fun k=>Q.extendedVertices (k+2);
    let Z:=fun k=>Q.extendedIndices (k+1);let W:=fun k=>Q.extendedIndices (k+2);
    let I:=markedVortexInnerVertices Q (i+1);let J:=markedVortexInnerHubs Q (i+1);
    let f:=markedVortexVertexEmbedding Q (i+1);let g:=markedVortexHubEmbedding Q (i+1);
    let ρ:=markedVortexPermutation Q π hπ (i+1);
    let Jwin:=Finset.Icc (i+2-2) i;
    OrdinaryProtectedTrace S H X T Z W cost deepCost (i+1) A→
    ordinaryHostResources G Hs=A→
    (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
    (∀u,(mWheel+1)∣(Finset.univ.filter (fun v=>Hs v u)).card)→
    βe*Fintype.card (markedVortexVertexType Q (i+1)⊕markedVortexHubType Q (i+1))+
      εR*I.card+3*(LF+∑j∈Jwin,cost j)≤pR^2*pH*(2*(θ+α-β/2)-1)*I.card→
    βh*Fintype.card (markedVortexVertexType Q (i+1)⊕markedVortexHubType Q (i+1))+
      εH*J.card+2*(LF+∑j∈Jwin,cost j)≤pH^2*J.card→
    (initialIndexDensity U D*pH)*β*I.card+εR*I.card+2*(εH*J.card)+
      3*(LF+∑j∈Jwin,cost j)≤ηbalance*I.card→
    OrdinaryCleanupParentProfiles (P.comap f) (G.comap f) (F.comap f)
      (fun v u=>Hs (f v) (g u)) ρ d I J pR pH (θ+α-β/2)
      (εR*I.card) (εH*J.card) (LF+∑j∈Jwin,cost j) βe βh (fun u=>s (g u)) j
      (ordinaryRawRestrictPair f g σ) ∧
    (∀a:markedVortexVertexType Q (i+1)⊕markedVortexHubType Q (i+1),
      ((changed ((ordinaryPhysicalGraph (rawWheelGraph (P.comap f) (ordinaryRawRestrictPair f g σ))
        (rawWheelSpokes ρ d (ordinaryRawRestrictPair f g σ) j)).neighborFinset a)
        ((ordinaryPhysicalGraph (G.comap f) (fun v u=>Hs (f v) (g u))).neighborFinset a)).card:ℝ)≤LF+∑k∈Jwin,cost k) ∧
    (∀v:I,|(((G.comap f).induce (I:Set _)).degree v:ℝ)-
      2*(Finset.univ.filter (fun u:J=>Hs (f v.val) (g u.val))).card|≤ηbalance*I.card) ∧
    (∀v∉I,|(((G.comap f).neighborFinset v∩I).card:ℝ)-
      2*(J.filter (fun u=>Hs (f v) (g u))).card|≤ηbalance*I.card) ∧
    (G.comap f)≤(P.comap f)\(F.comap f) ∧
    OrdinaryAdaptiveHubWeightsInnerScaleLevelEvent mWheel (P.comap f) (F.comap f) I J ρ d pR pH (θ+α-β/2)
      (εR*I.card) (εH*J.card) (LF+∑j∈Jwin,cost j) βe βh bHub BHub ηHub
      (fun u=>s (g u)) j (ordinaryRawRestrictPair f g σ) ∧
    Nonempty (OrdinaryMixedHubWeightsInnerScale mWheel bHub BHub ηHub (G.comap f) (F.comap f)
      (fun v u=>Hs (f v) (g u)) I J) ∧
    (∀v,(G.comap f).degree v=2*(Finset.univ.filter (fun u=>Hs (f v) (g u))).card) ∧
    (∀u,(mWheel+1)∣(Finset.univ.filter (fun v=>Hs (f v) (g u))).card) :=by
  intro F S H X T Z W I J f g ρ Jwin htrace hstate hbal hdiv hext hhub hmargin
  have hprofile:=ordinary_vortex_trace_buffered_profile_protected_pair P Gbase F Hbase D m β ε θ α pR pH εR εH
    Q π hπ d s j σ K Inner Hubs hInner hHubs hr hsample hK LF hLF hF
    hn hreg hρ hβ hpR hpR1 hpH hdensity hdegree hs hgood cost deepCost i 2 (by omega) hi A G Hs βe βh
    htrace hstate hext hhub
  have hL:0≤LF+∑k∈Jwin,cost k:=add_nonneg hLF (Finset.sum_nonneg (fun k _=>hcost k))
  have hcap':LF+∑k∈Jwin,cost k≤capHub*I.card:=by
    convert hcap using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hrest:=ordinary_protected_pair_trace_hub_balance mWheel P Gbase Hbase D m β ε Q π hπ d s j σ
    K Inner hInner hGbase hr pR pH (θ+α-β/2) εR εH βe βh bHub BHub ηHub capHub hfamily
    cost deepCost i hi A G Hs (LF+∑k∈Jwin,cost k) hL hcap' htrace hstate hbal hdiv
    (by convert hprofile using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
  have hphysical:=ordinary_protected_pair_trace_physical_edit P Gbase F Hbase D m β ε Q π hπ d j σ K Inner Hubs
    hInner hHubs hr hsample hK LF hLF hF cost deepCost i 2 (by omega) hi A G Hs htrace hstate
  have hnear:=ordinary_fixed_vortex_cleanup_balance P F D m β ε θ α pR pH εR εH
    (LF+∑k∈Jwin,cost k) βe βh ηbalance Q π hπ d s j σ hn hreg hρ hβ hpH hεR hεH hL hdegree hpEq hgood
    (i+1) hi (G.comap f) (fun v u=>Hs (f v) (g u))
    (by convert hprofile using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _) hmargin
  have hboth:=ordinary_fixed_vortex_cleanup_both_balance P F D m β ε θ α pR pH εR εH
    (LF+∑k∈Jwin,cost k) βe βh ηbalance Q π hπ d s j σ hn hreg hρ hβ hpH hεR hεH hL hdegree hpEq hgood
    (i+1) hi (G.comap f) (fun v u=>Hs (f v) (g u))
    (by convert hprofile using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _) hmargin
  refine ⟨?_,?_,?_,?_,?_⟩
  · convert hprofile using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  · convert hphysical using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  · convert hnear using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  · convert hboth.2 using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  · convert hrest using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
end Oberwolfach
