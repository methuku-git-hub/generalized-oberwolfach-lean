module

public import Oberwolfach.OrdinaryVortexTraceBufferedCleanupProfile
public import Oberwolfach.OrdinaryVortexCorrectionConflictEdits
public import Oberwolfach.OrdinaryFixedVortexCleanupBalance

@[expose] public section
/-! On the same raw sample, a protected initial correction and the actual
vortex trace supply both the local cleanup profile and its balance bound.
The only initial edit ∑j∈Jwin,cost js the permutation-conflict degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_vortex_protected_buffered_trace_local_balance
    (P JQ:SimpleGraph V) (JH:V→U→Prop) (D m:ℕ) (β ε θ α pR pH εR εH:ℝ)
    (Q:Vortex U P D β ε m) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d:ℕ) (s:U→Color→ℝ) (j:Color) (σ:RawWheelOutcome V U Γ Color)
    (hn:0<Fintype.card V) (hreg:P.IsRegularOfDegree D)
    (hρ:0< initialIndexDensity U D) (hβ:0≤β) (hpR:0≤pR) (hpR1:pR≤1) (hpH:0≤pH)
    (hεR:0≤εR) (hεH:0≤εH) (hdensity:1/2≤θ+α-β/2)
    (hdegree:(θ+α)*Fintype.card V≤D) (hpEq:pR=initialIndexDensity U D*pH)
    (hs:∀u,s u j=pH) (K:Finset (Sym2 V⊕(V×U)))
    (hJQ:∀v∈Q.extendedVertices 1,∀w∈Q.extendedVertices 1,¬JQ.Adj v w)
    (hJH:∀v u,JH v u→¬(v∈Q.extendedVertices 1 ∧ u∈Q.extendedIndices 1))
    (havoid:Disjoint K (ordinaryRootResources (Q.extendedVertices 1) (Q.extendedIndices 1)))
    (hgood:OrdinaryFixedVortexRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d))
      D m β ε Q π hπ pR pH s j σ)
    (cost deepCost:ℕ→ℝ) (i buffer:ℕ) (hbuffer:2≤buffer) (hi:i+1<Q.length)
    (A:Finset (Sym2 V⊕(V×U))) (G:SimpleGraph V) (Hs:V→U→Prop) (βe βh η:ℝ):
    let F:=permutationConflictGraph π (3*d);
    let R:=rawWheelGraph P σ;let J:=rawWheelSpokes π d σ j;
    let S:=(R\F)\JQ;let H:=fun v u=>J v u∧¬JH v u;
    let S₀:=S\ordinaryResourceRim S K;let H₀:=fun v u=>H v u∧¬(Sum.inr (v,u)∈K);
    let X:=fun k=>Q.extendedVertices (k+1);let T:=fun k=>Q.extendedVertices (k+buffer);
    let Z:=fun k=>Q.extendedIndices (k+1);let W:=fun k=>Q.extendedIndices (k+buffer);
    let I:=markedVortexInnerVertices Q (i+1);let B:=markedVortexInnerHubs Q (i+1);
    let f:=markedVortexVertexEmbedding Q (i+1);let g:=markedVortexHubEmbedding Q (i+1);
    let ρ:=markedVortexPermutation Q π hπ (i+1);
    let Jwin:=Finset.Icc (i+2-buffer) i;
    OrdinaryProtectedTrace S₀ H₀ X T Z W cost deepCost (i+1) A→
    ordinaryHostResources G Hs=A→0≤∑j∈Jwin,cost j→
    βe*Fintype.card (markedVortexVertexType Q (i+1)⊕markedVortexHubType Q (i+1))+
      εR*I.card+3*(2*((3*d:ℕ):ℝ)+∑j∈Jwin,cost j)≤pR^2*pH*(2*(θ+α-β/2)-1)*I.card→
    βh*Fintype.card (markedVortexVertexType Q (i+1)⊕markedVortexHubType Q (i+1))+
      εH*B.card+2*(2*((3*d:ℕ):ℝ)+∑j∈Jwin,cost j)≤pH^2*B.card→
    (initialIndexDensity U D*pH)*β*I.card+εR*I.card+2*(εH*B.card)+
      3*(2*((3*d:ℕ):ℝ)+∑j∈Jwin,cost j)≤η*I.card→
    OrdinaryCleanupParentProfiles (P.comap f) (G.comap f) (F.comap f)
      (fun v u=>Hs (f v) (g u)) ρ d I B pR pH (θ+α-β/2)
      (εR*I.card) (εH*B.card) (2*((3*d:ℕ):ℝ)+∑j∈Jwin,cost j) βe βh (fun u=>s (g u)) j
      (ordinaryRawRestrictPair f g σ) ∧
    (∀v:I,|(((G.comap f).induce (I:Set _)).degree v:ℝ)-
      2*(Finset.univ.filter (fun u:B=>Hs (f v.val) (g u.val))).card|≤η*I.card):=by
  intro F R J S H S₀ H₀ X T Z W I B f g ρ Jwin htrace hstate hcost hext hhub hmargin
  have hdis:Disjoint S₀ F:=by
    apply disjoint_iff_inf_le.mpr
    intro v w hvw
    exact hvw.1.1.1.2 hvw.2
  have hedits:=ordinary_vortex_correction_conflict_edits P R JQ D m β ε Q J JH K π (3*d) hJQ hJH havoid i
  have hprof:=ordinary_vortex_trace_buffered_cleanup_profile P S₀ F H₀ D m β ε θ α pR pH εR εH
    Q π hπ d s j σ hn hreg hρ hβ hpR hpR1 hpH hdensity hdegree hs hdis hgood
    cost deepCost i buffer hbuffer hi A G Hs (2*((3*d:ℕ):ℝ)) βe βh hedits htrace hstate hext hhub
  refine ⟨hprof,?_⟩
  have hL:0≤2*((3*d:ℕ):ℝ)+∑j∈Jwin,cost j:=by positivity
  exact ordinary_fixed_vortex_cleanup_balance P F D m β ε θ α pR pH εR εH
    (2*((3*d:ℕ):ℝ)+∑j∈Jwin,cost j) βe βh η Q π hπ d s j σ hn hreg hρ hβ hpH hεR hεH hL hdegree hpEq hgood
    (i+1) hi (G.comap f) (fun v u=>Hs (f v) (g u)) hprof hmargin
end Oberwolfach
