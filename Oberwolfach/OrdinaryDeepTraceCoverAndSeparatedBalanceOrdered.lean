module

public import Oberwolfach.OrdinaryVortexBufferedTraceSeparatedLinearCostAndRate
public import Oberwolfach.OrdinaryDeepTraceCoverAndBalanceOrdered

@[expose] public section
/-! Boundary rates are fixed linearly in the vortex scale before the cover's
later balance tolerance and the current trace are selected. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryDeepTraceSeparatedBalanceAt
    (ε ρ₀ α pmin hmin η ζ cBoundary δ rate:ℝ) (d buffer:ℕ) (β C:ℝ) (m₀:ℕ):Prop :=
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀(P JQ:SimpleGraph V) (JH:V→U→Prop) (D m:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→m₀≤m→
    ∀(Q:Vortex U P D β ε m) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (s:U→Color→ℝ) (j:Color) (σ:RawWheelOutcome V U Γ Color)
      (pR pH θ εR εH βe βh:ℝ),pmin≤pR→pR≤1→hmin≤pH→1/2≤θ→(θ+α)*Fintype.card V≤D→
      pR=initialIndexDensity U D*pH→(∀u,s u j=pH)→
      0≤εR→εR≤δ→0≤εH→εH≤δ→0≤βe→βe≤cBoundary*ε→0≤βh→βh≤cBoundary*ε→
    ∀(K:Finset (Sym2 V⊕(V×U))),
      (∀v∈Q.extendedVertices 1,∀w∈Q.extendedVertices 1,¬JQ.Adj v w)→
      (∀v u,JH v u→¬(v∈Q.extendedVertices 1 ∧ u∈Q.extendedIndices 1))→
      Disjoint K (ordinaryRootResources (Q.extendedVertices 1) (Q.extendedIndices 1))→
      OrdinaryFixedVortexRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d))
        D m β ε Q π hπ pR pH s j σ→
    ∀(cost deepCost:ℕ→ℝ) (i:ℕ),i+1<Q.length→
    ∀(A:Finset (Sym2 V⊕(V×U))) (G:SimpleGraph V) (Hs:V→U→Prop),
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
    ordinaryHostResources G Hs=A→
    (∀j∈Jwin,0≤cost j ∧ cost j≤4*rate*Fintype.card (markedVortexVertexType Q j⊕markedVortexHubType Q j)+C)→
    0≤(∑j∈Jwin,cost j) ∧ (∑j∈Jwin,cost j)≤δ*I.card ∧ (∑j∈Jwin,cost j)≤δ*B.card ∧
    OrdinaryCleanupParentProfiles (P.comap f) (G.comap f) (F.comap f)
      (fun v u=>Hs (f v) (g u)) ρ d I B pR pH (θ+α-β/2)
      (εR*I.card) (εH*B.card) (2*((3*d:ℕ):ℝ)+(∑j∈Jwin,cost j)) βe βh (fun u=>s (g u)) j
      (ordinaryRawRestrictPair f g σ) ∧
    (∀v:I,|(((G.comap f).induce (I:Set _)).degree v:ℝ)-
      2*(Finset.univ.filter (fun u:B=>Hs (f v.val) (g u.val))).card|≤η*I.card) ∧
    (initialIndexDensity U D*pH)*β*I.card+εR*I.card+2*(εH*B.card)+
      3*(2*((3*d:ℕ):ℝ)+(∑j∈Jwin,cost j))≤η*I.card ∧
    2*((3*d:ℕ):ℝ)+(∑j∈Jwin,cost j)≤ζ*I.card ∧
    2*((3*d:ℕ):ℝ)+(∑j∈Jwin,cost j)≤ζ*Fintype.card (markedVortexVertexType Q (i+1))

theorem ordinary_deep_trace_cover_and_separated_balance_ordered
    (mWheel K buffer:ℕ) (hm:3≤mWheel) (hbuffer:2≤buffer)
    (ρ₀ hmin href δlimit a ρ θ α pmin:ℝ) (d:ℕ)
    (hρ₀:0<ρ₀) (hhmin:0<hmin) (hhref:0<href) (hδlimit:0<δlimit)
    (ha:0<a) (hρ:0<ρ) (hθ:0<θ) (hα:0<α) (hpmin:0<pmin):
    ∃δcut ζcut εcut ζlimit εsample εvortex cBoundary:ℝ,
      0<δcut ∧ δcut<1/4 ∧ δcut≤δlimit ∧ 0<ζcut ∧ 0<εcut ∧ 0<ζlimit ∧
      0<εsample ∧ 0<εvortex ∧ εvortex<1/4 ∧ 0<cBoundary ∧
    ∀ε:ℝ,0<ε→ε≤εvortex→∀aLoad:ℝ,0<aLoad→aLoad≤1→
    ∃ξ η₀:ℝ,0<ξ ∧ 0<η₀ ∧ ∀η:ℝ,0<η→η≤η₀→∀rateParent:ℝ,0<rateParent→
    ∃ζ δ rate:ℝ,0<ζ ∧ ζ≤ζlimit ∧ ζ≤rateParent ∧ 0<δ ∧ δ≤α ∧ 0<rate ∧
    ∀β:ℝ,0≤β→β≤1/4→β≤δ→∀C:ℝ,0≤C→
    ∃mBalance mCover:ℕ,1≤mBalance ∧ 1≤mCover ∧
      OrdinaryDeepTraceSeparatedBalanceAt ε ρ₀ α pmin hmin η ζ cBoundary δ rate d buffer β C mBalance ∧
      OrdinaryDeepTraceCoverAt mWheel K buffer ρ₀ hmin href δcut ζcut εcut ζlimit εsample ε ξ aLoad a ρ θ β η d mCover :=by
  obtain ⟨δcut,ζcut,εcut,ζlimit,εsample,εvortex,hδcut,hδcut1,hδlimit',hζcut,hεcut,hζlimit,hεsample,hεvortex,hεvortex1,hcover⟩:=
    ordinary_vortex_deep_trace_nonroot_numeric_balance_before_beta mWheel K buffer hm hbuffer ρ₀ hmin href δlimit a ρ θ
      hρ₀ hhmin hhref hδlimit ha hρ hθ
  obtain ⟨cBoundary,hcBoundary,hbalance⟩:=ordinary_vortex_buffered_trace_separated_linear_cost_and_rate
    ρ₀ α pmin hmin d buffer hbuffer hρ₀ hα hpmin hhmin
  refine ⟨δcut,ζcut,εcut,ζlimit,εsample,εvortex,cBoundary,hδcut,hδcut1,hδlimit',hζcut,hεcut,hζlimit,hεsample,hεvortex,hεvortex1,hcBoundary,?_⟩
  intro ε hε hεvortex aLoad haLoad haLoad1
  obtain ⟨ξ,η₀,hξ,hη₀,hcover⟩:=hcover ε hε hεvortex aLoad haLoad haLoad1
  refine ⟨ξ,η₀,hξ,hη₀,?_⟩
  intro η hη hη0 rateParent hrate
  let ζ:ℝ:=min ζlimit rateParent
  have hζ:0<ζ:=lt_min hζlimit hrate
  obtain ⟨δ,rate,hδ,hδα,hrateC,hbalance⟩:=hbalance ε hε (lt_of_le_of_lt hεvortex hεvortex1) η ζ hη hζ
  refine ⟨ζ,δ,rate,hζ,min_le_left _ _,min_le_right _ _,hδ,hδα,hrateC,?_⟩
  intro β hβ hβ1 hβδ C hC
  obtain ⟨mb,hmb,hbalance⟩:=hbalance β hβ hβ1 hβδ C hC
  obtain ⟨mc,hmc,hcover⟩:=hcover β hβ hβ1 d
  exact ⟨mb,mc,hmb,hmc,hbalance,hcover η hη.le hη0⟩
end Oberwolfach
