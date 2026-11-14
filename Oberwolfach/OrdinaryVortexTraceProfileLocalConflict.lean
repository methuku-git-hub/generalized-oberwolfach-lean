module

public import Oberwolfach.OrdinaryTraceCleanupProfileLocalConflict
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

theorem ordinary_vortex_trace_buffered_cleanup_profile_local_conflict
    (P S F:SimpleGraph V) (H:V→U→Prop) (D m:ℕ) (β ε θ α pR pH εR εH:ℝ)
    (Q:Vortex U P D β ε m) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d:ℕ) (s:U→Color→ℝ) (j:Color) (σ:RawWheelOutcome V U Γ Color)
    (hn:0<Fintype.card V) (hreg:P.IsRegularOfDegree D)
    (hρ:0< initialIndexDensity U D) (hβ:0≤β) (hpR:0≤pR) (hpR1:pR≤1) (hpH:0≤pH)
    (hdensity:1/2≤θ+α-β/2) (hdegree:(θ+α)*Fintype.card V≤D)
    (hs:∀u,s u j=pH)
    (hSF:∀i,i+1<Q.length→Disjoint (S.induce ((Q.extendedVertices (i+1)):Set V))
      (F.induce ((Q.extendedVertices (i+1)):Set V)))
    (hgood:OrdinaryFixedVortexRowIndexEvent 3 d εR εH P F D m β ε Q π hπ pR pH s j σ)
    (cost deepCost:ℕ→ℝ) (i buffer:ℕ) (hbuffer:2≤buffer) (hi:i+1<Q.length)
    (A:Finset (Sym2 V⊕(V×U))) (G:SimpleGraph V) (Hs:V→U→Prop) (L βe βh:ℝ):
    let X:=fun k=>Q.extendedVertices (k+1);let T:=fun k=>Q.extendedVertices (k+buffer);
    let Z:=fun k=>Q.extendedIndices (k+1);let W:=fun k=>Q.extendedIndices (k+buffer);
    let I:=markedVortexInnerVertices Q (i+1);let J:=markedVortexInnerHubs Q (i+1);
    let f:=markedVortexVertexEmbedding Q (i+1);let g:=markedVortexHubEmbedding Q (i+1);
    let ρ:=markedVortexPermutation Q π hπ (i+1);
    let Jwin:=Finset.Icc (i+2-buffer) i;
    (∀a:↥(X i)⊕↥(Z i),
      ((changed ((ordinaryPhysicalGraph ((rawWheelGraph P σ).induce ((X i):Set V))
        (fun (v:↥(X i)) (u:↥(Z i))=>rawWheelSpokes π d σ j v.val u.val)).neighborFinset a)
        ((ordinaryPhysicalGraph (S.induce ((X i):Set V))
        (fun (v:↥(X i)) (u:↥(Z i))=>H v.val u.val)).neighborFinset a)).card:ℝ)≤L)→
    OrdinaryProtectedTrace S H X T Z W cost deepCost (i+1) A→
    ordinaryHostResources G Hs=A→
    βe*Fintype.card (markedVortexVertexType Q (i+1)⊕markedVortexHubType Q (i+1))+
      εR*I.card+3*(L+∑j∈Jwin,cost j)≤pR^2*pH*(2*(θ+α-β/2)-1)*I.card→
    βh*Fintype.card (markedVortexVertexType Q (i+1)⊕markedVortexHubType Q (i+1))+
      εH*J.card+2*(L+∑j∈Jwin,cost j)≤pH^2*J.card→
    OrdinaryCleanupParentProfiles (P.comap f) (G.comap f) (F.comap f)
      (fun v u=>Hs (f v) (g u)) ρ d I J pR pH (θ+α-β/2)
      (εR*I.card) (εH*J.card) (L+∑j∈Jwin,cost j) βe βh (fun u=>s (g u)) j
      (ordinaryRawRestrictPair f g σ):=by
  intro X T Z W I J f g ρ Jwin hbase htrace hstate hext hhub
  have hinputs:=ordinary_fixed_vortex_cleanup_inputs P F D m β ε θ α pR pH εR εH Q π hπ d s j σ
    hn hreg hρ hβ hpH hdegree hgood (i+1) hi
  have hnest:=ordinary_vortex_buffered_nesting P D m β ε Q i buffer hbuffer
  have hh:=ordinary_trace_cleanup_profile_from_local_conflict P S F H π d j σ X T Z W cost deepCost i Jwin A G Hs
    ρ (by intro x; rfl) I J pR pH (θ+α-β/2) (εR*I.card) (εH*J.card) L βe βh s
    hpR hpR1 hpH hdensity hs (hSF i hi) hbase htrace hstate hnest.1 hnest.2.1 hnest.2.2.1 hnest.2.2.2.1 hnest.2.2.2.2
  apply hh
  · exact hinputs.1
  · exact hinputs.2.2.1
  · exact hinputs.2.2.2
  · exact hext
  · exact hhub
end Oberwolfach
