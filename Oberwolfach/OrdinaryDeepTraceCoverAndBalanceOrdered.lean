module

public import Oberwolfach.OrdinaryVortexBufferedTraceBalanceCostMarginAndRate
public import Oberwolfach.OrdinaryVortexDeepTraceNonrootNumericBalanceBeforeBeta

@[expose] public section
/-! Choose the deeper cover tolerance before the vortex error, and then
select compatible trace-edit tolerances and size thresholds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryDeepTraceBalanceAt
    (ε ρ₀ α pmin hmin η ζ δ rate:ℝ) (d buffer:ℕ) (β C:ℝ) (m₀:ℕ):Prop :=
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀(P JQ:SimpleGraph V) (JH:V→U→Prop) (D m:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→m₀≤m→
    ∀(Q:Vortex U P D β ε m) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (s:U→Color→ℝ) (j:Color) (σ:RawWheelOutcome V U Γ Color)
      (pR pH θ εR εH βe βh:ℝ),pmin≤pR→pR≤1→hmin≤pH→1/2≤θ→(θ+α)*Fintype.card V≤D→
      pR=initialIndexDensity U D*pH→(∀u,s u j=pH)→
      0≤εR→εR≤δ→0≤εH→εH≤δ→0≤βe→βe≤δ→0≤βh→βh≤δ→
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

def OrdinaryDeepTraceCoverAt
    (mWheel K buffer:ℕ) (ρ₀ pmin href δcut ζcut εcut ζlimit εsample ε ξ aLoad a ρ θ β η:ℝ)
    (d m₀:ℕ):Prop :=
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [LinearOrder U],
    ∀(P JQ G:SimpleGraph V) (JH Hs:V→U→Prop) (D vsize:ℕ),
      P.IsRegularOfDegree D→0<Fintype.card V→(Fintype.card V:ℝ)/2≤D→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→m₀≤vsize→
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (σ:RawWheelOutcome V U Γ Color) (coins:Sym2 V→Bool) (j:Color) (s:U→Color→ℝ)
      (Kres:Finset (Sym2 V⊕(V×U))) (cost deepCost:ℕ→ℝ) (i:ℕ),i+1<Q.length→
    ∀(A:Finset (Sym2 V⊕(V×U))) (pR pH density εR εH Ledit βe βh αcut pstar θhost αhost:ℝ),
    let f:markedVortexVertexType Q (i+1)↪V:=(markedVortexVertexEmbedding Q (i+1)).toEmbedding;
    let g:=markedVortexHubEmbedding Q (i+1);let I:=markedVortexInnerVertices Q (i+1);let T:=ordinaryVortexBufferedVertices Q (i+1) buffer;
    let B:=markedVortexInnerHubs Q (i+1);let W:=ordinaryVortexBufferedHubs Q (i+1) buffer;
    let ρi:=markedVortexPermutation Q π hπ (i+1);
    let Ploc:=P.comap f;let Floc:=(permutationConflictGraph π (3*d)).comap f;
    let Gloc:=G.comap f;let Hloc:=fun v u=>Hs (f v) (g u);
    let localRaw:=ordinaryRawRestrictPair f g σ;
    let localCoins:=fun e:Sym2 (markedVortexVertexType Q (i+1))=>coins (Sym2.map f e);
    let R:=rawWheelGraph P σ;let J:=rawWheelSpokes π d σ j;
    let S:=(R\permutationConflictGraph π (3*d))\JQ;let H:=fun v u=>J v u∧¬JH v u;
    let S₀:=S\ordinaryResourceRim S Kres;let H₀:=fun v u=>H v u∧¬(Sum.inr (v,u)∈Kres);
    let X:=fun k=>Q.extendedVertices (k+1);let Tdeep:=fun k=>Q.extendedVertices (k+buffer);
    let Z:=fun k=>Q.extendedIndices (k+1);let Wdeep:=fun k=>Q.extendedIndices (k+buffer);
    pmin≤pH→εR≤εsample→εH≤εsample→Ledit≤ζlimit*I.card→
    OrdinaryCleanupParentProfiles Ploc Gloc Floc Hloc ρi d I B pR pH density (εR*I.card) (εH*B.card) Ledit βe βh (fun u=>s (g u)) j localRaw→
    density=θhost+αhost-β/2→0≤εR→0≤εH→(θhost+αhost)*Fintype.card V≤D→
    pR=initialIndexDensity U D*pH→
    OrdinaryFixedVortexRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d)) D vsize β ε Q π hπ pR pH s j σ→
    (initialIndexDensity U D*pH)*β*I.card+εR*I.card+2*(εH*B.card)+3*Ledit≤η*I.card→
    OrdinaryProtectedTrace S₀ H₀ X Tdeep Z Wdeep cost deepCost (i+1) A→ ordinaryHostResources G Hs=A→
    (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→(∀u,(mWheel+1)∣(Finset.univ.filter (fun v=>Hs v u)).card)→
    OrdinaryFixedVortexDeepCoverEvent mWheel K d a aLoad ρ θ P D vsize β ε Q π hπ j σ→
    OrdinaryInducedRimCutEvent (Q.extendedVertices (i+2)) (sampledOrientation (rawWheelGraph P σ) coins) αcut pstar→
    0<pH→pH≤1→0≤εcut→0≤ζcut→0≤ζlimit→0≤Ledit→
    δcut≤min (αcut/32) (pstar/512)→href≤αcut*pstar/64→
    OrdinaryNonrootWheelCoverResult mWheel K ξ aLoad Gloc Floc Hloc I T B W

theorem ordinary_deep_trace_cover_and_balance_ordered
    (mWheel K buffer:ℕ) (hm:3≤mWheel) (hbuffer:2≤buffer)
    (ρ₀ hmin href δlimit a ρ θ:ℝ)
    (hρ₀:0<ρ₀) (hhmin:0<hmin) (hhref:0<href) (hδlimit:0<δlimit)
    (ha:0<a) (hρ:0<ρ) (hθ:0<θ):
    ∃δcut ζcut εcut ζlimit εsample εvortex:ℝ,
      0<δcut ∧ δcut<1/4 ∧ δcut≤δlimit ∧ 0<ζcut ∧ 0<εcut ∧ 0<ζlimit ∧
      0<εsample ∧ 0<εvortex ∧ εvortex<1/4 ∧
    ∀ε:ℝ,0<ε→ε≤εvortex→∀aLoad:ℝ,0<aLoad→aLoad≤1→
    ∃ξ η₀:ℝ,0<ξ ∧ 0<η₀ ∧ ∀η:ℝ,0<η→η≤η₀→
    ∀(α pmin ζ:ℝ),0<α→0<pmin→0<ζ→∀d:ℕ,
    ∃δ rate:ℝ,0<δ ∧ δ≤α ∧ 0<rate ∧
    ∀β:ℝ,0≤β→β≤1/4→β≤δ→∀C:ℝ,0≤C→
    ∃mBalance mCover:ℕ,1≤mBalance ∧ 1≤mCover ∧
      OrdinaryDeepTraceBalanceAt ε ρ₀ α pmin hmin η ζ δ rate d buffer β C mBalance ∧
      OrdinaryDeepTraceCoverAt mWheel K buffer ρ₀ hmin href δcut ζcut εcut ζlimit εsample ε ξ aLoad a ρ θ β η d mCover :=by
  obtain ⟨δcut,ζcut,εcut,ζlimit,εsample,εvortex,hδcut,hδcut1,hδlimit',hζcut,hεcut,hζlimit,hεsample,hεvortex,hεvortex1,hcover⟩:=
    ordinary_vortex_deep_trace_nonroot_numeric_balance_before_beta mWheel K buffer hm hbuffer ρ₀ hmin href δlimit a ρ θ
      hρ₀ hhmin hhref hδlimit ha hρ hθ
  refine ⟨δcut,ζcut,εcut,ζlimit,εsample,εvortex,hδcut,hδcut1,hδlimit',hζcut,hεcut,hζlimit,hεsample,hεvortex,hεvortex1,?_⟩
  intro ε hε hεvortex aLoad haLoad haLoad1
  obtain ⟨ξ,η₀,hξ,hη₀,hcover⟩:=hcover ε hε hεvortex aLoad haLoad haLoad1
  refine ⟨ξ,η₀,hξ,hη₀,?_⟩
  intro η hη hη0 α pmin ζ hα hpmin hζ d
  obtain ⟨δ,rate,hδ,hδα,hrate,hbalance⟩:=ordinary_vortex_buffered_trace_balance_cost_margin_and_rate ε ρ₀ α pmin hmin η ζ d buffer hbuffer
    hε (lt_of_le_of_lt hεvortex hεvortex1) hρ₀ hα hpmin hhmin hη hζ
  refine ⟨δ,rate,hδ,hδα,hrate,?_⟩
  intro β hβ hβ1 hβδ C hC
  obtain ⟨mb,hmb,hbalance⟩:=hbalance β hβ hβ1 hβδ C hC
  obtain ⟨mc,hmc,hcover⟩:=hcover β hβ hβ1 d
  refine ⟨mb,mc,hmb,hmc,hbalance,?_⟩
  exact hcover η hη.le hη0
end Oberwolfach
