module

public import Oberwolfach.OrdinaryVortexTraceProfileLocalConflict
public import Oberwolfach.OrdinaryProtectedSamplePairLocalInputs
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

theorem ordinary_vortex_trace_buffered_profile_protected_pair
    (P Gbase F:SimpleGraph V) (Hbase:V→U→Prop) (D m:ℕ) (β ε θ α pR pH εR εH:ℝ)
    (Q:Vortex U P D β ε m) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d:ℕ) (s:U→Color→ℝ) (j:Color) (σ:RawWheelOutcome V U Γ Color)
    (K:Finset (Sym2 V⊕(V×U))) (Inner:Finset V) (Hubs:Finset U)
    (hInner:Q.extendedVertices 1⊆Inner) (hHubs:Q.extendedIndices 1⊆Hubs)
    (hr:∀v∈Inner,∀w∈Inner,((rawWheelGraph P σ)\F).Adj v w↔Gbase.Adj v w)
    (hsample:∀v∈Inner,∀u∈Hubs,rawWheelSpokes π d σ j v u↔Hbase v u)
    (hK:Disjoint K (ordinaryRootResources Inner Hubs))
    (LF:ℝ) (hLF:0≤LF) (hF:∀v,(F.degree v:ℝ)≤LF)
    (hn:0<Fintype.card V) (hreg:P.IsRegularOfDegree D)
    (hρ:0< initialIndexDensity U D) (hβ:0≤β) (hpR:0≤pR) (hpR1:pR≤1) (hpH:0≤pH)
    (hdensity:1/2≤θ+α-β/2) (hdegree:(θ+α)*Fintype.card V≤D)
    (hs:∀u,s u j=pH)
    (hgood:OrdinaryFixedVortexRowIndexEvent 3 d εR εH P F D m β ε Q π hπ pR pH s j σ)
    (cost deepCost:ℕ→ℝ) (i buffer:ℕ) (hbuffer:2≤buffer) (hi:i+1<Q.length)
    (A:Finset (Sym2 V⊕(V×U))) (G:SimpleGraph V) (Hs:V→U→Prop) (βe βh:ℝ):
    let S:=Gbase\ordinaryResourceRim Gbase K;
    let H:=fun v u=>Hbase v u∧¬(Sum.inr (v,u)∈K);
    let X:=fun k=>Q.extendedVertices (k+1);let T:=fun k=>Q.extendedVertices (k+buffer);
    let Z:=fun k=>Q.extendedIndices (k+1);let W:=fun k=>Q.extendedIndices (k+buffer);
    let I:=markedVortexInnerVertices Q (i+1);let J:=markedVortexInnerHubs Q (i+1);
    let f:=markedVortexVertexEmbedding Q (i+1);let g:=markedVortexHubEmbedding Q (i+1);
    let ρ:=markedVortexPermutation Q π hπ (i+1);
    let Jwin:=Finset.Icc (i+2-buffer) i;
    OrdinaryProtectedTrace S H X T Z W cost deepCost (i+1) A→
    ordinaryHostResources G Hs=A→
    βe*Fintype.card (markedVortexVertexType Q (i+1)⊕markedVortexHubType Q (i+1))+
      εR*I.card+3*(LF+∑j∈Jwin,cost j)≤pR^2*pH*(2*(θ+α-β/2)-1)*I.card→
    βh*Fintype.card (markedVortexVertexType Q (i+1)⊕markedVortexHubType Q (i+1))+
      εH*J.card+2*(LF+∑j∈Jwin,cost j)≤pH^2*J.card→
    OrdinaryCleanupParentProfiles (P.comap f) (G.comap f) (F.comap f)
      (fun v u=>Hs (f v) (g u)) ρ d I J pR pH (θ+α-β/2)
      (εR*I.card) (εH*J.card) (LF+∑j∈Jwin,cost j) βe βh (fun u=>s (g u)) j
      (ordinaryRawRestrictPair f g σ):=by
  intro S H X T Z W I J f g ρ Jwin htrace hstate hext hhub
  have hloc:∀t,t+1<Q.length→
      Disjoint (S.induce ((Q.extendedVertices (t+1)):Set V))
        (F.induce ((Q.extendedVertices (t+1)):Set V)) ∧
      ∀a:↥(Q.extendedVertices (t+1))⊕↥(Q.extendedIndices (t+1)),
        ((changed ((ordinaryPhysicalGraph ((rawWheelGraph P σ).induce ((Q.extendedVertices (t+1)):Set V))
          (fun (v:↥(Q.extendedVertices (t+1))) (u:↥(Q.extendedIndices (t+1)))=>rawWheelSpokes π d σ j v.val u.val)).neighborFinset a)
          ((ordinaryPhysicalGraph (S.induce ((Q.extendedVertices (t+1)):Set V))
          (fun (v:↥(Q.extendedVertices (t+1))) (u:↥(Q.extendedIndices (t+1)))=>H v.val u.val)).neighborFinset a)).card:ℝ)≤LF:=by
    intro t ht
    have hX:Q.extendedVertices (t+1)⊆Inner:=
      (Q.extendedVertices_subset (by omega : 1≤t+1)).trans hInner
    have hZ:Q.extendedIndices (t+1)⊆Hubs:=
      (Q.extendedIndices_subset (by omega : 1≤t+1)).trans hHubs
    have hh:=ordinary_protected_sample_pair_local_inputs (rawWheelGraph P σ) F Gbase
      (rawWheelSpokes π d σ j) Hbase K (Q.extendedVertices (t+1)) Inner (Q.extendedIndices (t+1)) Hubs
      hX hZ hr hsample hK LF hLF hF
    convert hh using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  have hSF:∀t,t+1<Q.length→Disjoint (S.induce ((Q.extendedVertices (t+1)):Set V))
      (F.induce ((Q.extendedVertices (t+1)):Set V)):=fun t ht=>(hloc t ht).1
  have hbase:∀a:↥(X i)⊕↥(Z i),
      ((changed ((ordinaryPhysicalGraph ((rawWheelGraph P σ).induce ((X i):Set V))
        (fun (v:↥(X i)) (u:↥(Z i))=>rawWheelSpokes π d σ j v.val u.val)).neighborFinset a)
        ((ordinaryPhysicalGraph (S.induce ((X i):Set V))
        (fun (v:↥(X i)) (u:↥(Z i))=>H v.val u.val)).neighborFinset a)).card:ℝ)≤LF:=by
    intro a
    have hh:=(hloc i hi).2 a
    convert hh using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  exact ordinary_vortex_trace_buffered_cleanup_profile_local_conflict P S F H D m β ε θ α pR pH εR εH
    Q π hπ d s j σ hn hreg hρ hβ hpR hpR1 hpH hdensity hdegree hs hSF hgood
    cost deepCost i buffer hbuffer hi A G Hs LF βe βh hbase htrace hstate hext hhub
end Oberwolfach
