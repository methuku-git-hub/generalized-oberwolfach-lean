module

public import Oberwolfach.OrdinaryExpandedTwoStepVortexTestsAttach
public import Oberwolfach.OrdinaryVortexDeepSampleBalance
public import Oberwolfach.OrdinaryVortexTraceParentDirectEdits

@[expose] public section
/-! On the actual protected trace, the two-step tests provide the deep
cross-balance needed by the sharper nonroot reference geometry. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_vortex_trace_deep_sample_balance
    (P JQ:SimpleGraph V) (JH:V→U→Prop) (D m:ℕ) (β ε pR pH εR εH:ℝ)
    (Q:Vortex U P D β ε m) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d:ℕ) (s:U→Color→ℝ) (j:Color) (σ:RawWheelOutcome V U Γ Color) (K:Finset (Sym2 V⊕(V×U)))
    (hn:0<Fintype.card V) (hreg:P.IsRegularOfDegree D) (hρ:0< initialIndexDensity U D)
    (hβ:0≤β) (hpH:0≤pH) (hεR:0≤εR) (hεH:0≤εH) (hpR:pR=initialIndexDensity U D*pH)
    (hJQ:∀v∈Q.extendedVertices 1,∀w∈Q.extendedVertices 1,¬JQ.Adj v w)
    (hJH:∀v u,JH v u→¬(v∈Q.extendedVertices 1 ∧ u∈Q.extendedIndices 1))
    (havoid:Disjoint K (ordinaryRootResources (Q.extendedVertices 1) (Q.extendedIndices 1)))
    (hgood:OrdinaryVortexTwoStepRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d))
      D m β ε Q π hπ pR pH s j σ)
    (cost deepCost:ℕ→ℝ) (i:ℕ) (hi:i+1<Q.length) (hcost:0≤cost i)
    (A:Finset (Sym2 V⊕(V×U))) (G:SimpleGraph V) (Hs:V→U→Prop):
    let F:=permutationConflictGraph π (3*d)
    let R:=rawWheelGraph P σ;let J:=rawWheelSpokes π d σ j
    let S:=(R\F)\JQ;let H:=fun v u=>J v u∧¬JH v u
    let S₀:=S\ordinaryResourceRim S K;let H₀:=fun v u=>H v u∧¬(Sum.inr (v,u)∈K)
    let X:=fun k=>Q.extendedVertices (k+1);let T:=fun k=>Q.extendedVertices (k+2)
    let Z:=fun k=>Q.extendedIndices (k+1);let W:=fun k=>Q.extendedIndices (k+2);
    OrdinaryProtectedTrace S₀ H₀ X T Z W cost deepCost (i+1) A → ordinaryHostResources G Hs=A→
    let f:=markedVortexVertexEmbedding Q (i+1);let g:=markedVortexHubEmbedding Q (i+1)
    let Tlocal:=ordinaryVortexBufferedVertices Q (i+1) 2;let Wlocal:=ordinaryVortexBufferedHubs Q (i+1) 2
    let Hlocal:=fun v u=>Hs (f v) (g u);
    ∀v,|(((G.comap f).neighborFinset v∩Tlocal).card:ℝ)-2*(Wlocal.filter (Hlocal v)).card|≤
      (initialIndexDensity U D*pH)*β*Tlocal.card+εR*Tlocal.card+2*(εH*Wlocal.card)+3*(2*((3*d:ℕ):ℝ)+cost i):=by
  intro F R J S H S₀ H₀ X T Z W htrace hstate f g Tlocal Wlocal Hlocal v
  have hL:0≤2*((3*d:ℕ):ℝ)+cost i:=by positivity
  by_cases htarget:i+1+2≤Q.length
  · have tests:=hgood (i+1) htarget
    have hrows:RawOrdinaryRows (P.comap f) (markedVortexPermutation Q π hπ (i+1)) d 2 Tlocal pR
        (fun u=>s (g u)) j (εR*Tlocal.card) (ordinaryRawRestrictPair f g σ):=by
      intro S J hS hJ
      exact tests.1 S J (by omega) (by omega)
    have hedits:=ordinary_vortex_trace_parent_direct_edits P JQ JH D m β ε Q π hπ d j σ K hJQ hJH havoid
      cost deepCost i A G Hs htrace hstate
    have hrim:∀x,((changed ((G.comap f).neighborFinset x)
        ((rawWheelGraph (P.comap f) (ordinaryRawRestrictPair f g σ)).neighborFinset x)).card:ℝ)≤2*((3*d:ℕ):ℝ)+cost i:=by
      intro x
      simpa [changed,Finset.union_comm] using hedits.1 x
    have hspoke:∀x,((changed (Finset.univ.filter (Hlocal x))
        (Finset.univ.filter (rawWheelSpokes (markedVortexPermutation Q π hπ (i+1)) d (ordinaryRawRestrictPair f g σ) j x))).card:ℝ)≤2*((3*d:ℕ):ℝ)+cost i:=by
      intro x
      simpa [changed,Finset.union_comm] using hedits.2.1 x
    exact ordinary_vortex_deep_sample_balance P F D m β ε pR pH εR εH (2*((3*d:ℕ):ℝ)+cost i)
      Q π hπ d s j σ hn hreg hρ hβ hpH hεR hεH hL hpR (i+1) (G.comap f) Hlocal
      hrows tests.2 hrim hspoke v
  · have hV:Q.extendedVertices (i+1+2)=∅:=Q.extendedVertices_empty (by omega)
    have hU:Q.extendedIndices (i+1+2)=∅:=Q.extendedIndices_empty (by omega)
    have hT:Tlocal=∅:=by simp [Tlocal,ordinaryVortexBufferedVertices,hV]
    have hW:Wlocal=∅:=by simp [Wlocal,ordinaryVortexBufferedHubs,hU]
    simp only [hT,hW,Finset.inter_empty,Finset.filter_empty,Finset.card_empty,Nat.cast_zero,mul_zero,sub_zero,abs_zero,zero_add]
    positivity
end Oberwolfach
