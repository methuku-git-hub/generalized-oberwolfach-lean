module

public import Oberwolfach.OrdinaryProtectedPairReserveAgreement
public import Oberwolfach.OrdinaryVortexInitialDeepSampleBalance
public import Oberwolfach.OrdinaryVortexUniformHistoryDeepTargetCross
public import Oberwolfach.OrdinaryCrossBalanceInducedReverse

@[expose] public section
/-! The two-step deeper cross balance on the current parent is inherited
from the original sample and the deep-boundary cost of the preceding level. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_vortex_actual_uniform_two_step_deep_balance
    (P Gbase:SimpleGraph V) (Hbase:V→U→Prop) (D m:ℕ) (β ε pR pH εR εH:ℝ)
    (Q:Vortex U P D β ε m) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d:ℕ) (s:U→Color→ℝ) (j:Color) (σ:RawWheelOutcome V U Γ Color) (K:Finset (Sym2 V⊕(V×U)))
    (hn:0<Fintype.card V) (hreg:P.IsRegularOfDegree D) (hρ:0< initialIndexDensity U D)
    (hβ:0≤β) (hpH:0≤pH) (hεR:0≤εR) (hεH:0≤εH) (hpR:pR=initialIndexDensity U D*pH)
    (hPairRim:∀v∈Q.extendedVertices 1,∀w∈Q.extendedVertices 1,
      ((rawWheelGraph P σ)\permutationConflictGraph π (3*d)).Adj v w↔Gbase.Adj v w)
    (hPairSpoke:∀v∈Q.extendedVertices 1,∀u∈Q.extendedIndices 1,
      rawWheelSpokes π d σ j v u↔Hbase v u)
    (havoid:Disjoint K (ordinaryRootResources (Q.extendedVertices 1) (Q.extendedIndices 1)))
    (hgood:OrdinaryVortexTwoStepRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d))
      D m β ε Q π hπ pR pH s j σ)
    (r i L:ℕ) (hi:i+1<Q.length) (hiL:i<L) (cost deepCost:ℕ→ℝ)
    (A:Finset (Sym2 V⊕(V×U))) (G:SimpleGraph V) (Hs:V→U→Prop) (inner cross:ℕ→ℕ→ℝ):
    let F:=permutationConflictGraph π (3*d)
    let R:=rawWheelGraph P σ;let J:=rawWheelSpokes π d σ j
    let S:=Gbase;let H:=Hbase
    let S₀:=S\ordinaryResourceRim S K;let H₀:=fun v u=>H v u∧¬(Sum.inr (v,u)∈K)
    let X:=fun k=>Q.extendedVertices (k+1);let T:=fun k=>Q.extendedVertices (k+2)
    let Z:=fun k=>Q.extendedIndices (k+1);let W:=fun k=>Q.extendedIndices (k+2);
    OrdinaryUniformProtectedBalanceHistory S₀ H₀ X T Z W cost deepCost r (i+1) L A
      (fun t=>Q.extendedVertices (t+2)) (fun t=>Q.extendedVertices (t+1))
      (fun t=>Q.extendedIndices (t+2)) (fun t=>Finset.Icc (t+3-2) t) inner cross→
    ordinaryHostResources G Hs=A→
    let f:=markedVortexVertexEmbedding Q (i+1);let g:=markedVortexHubEmbedding Q (i+1)
    let Tlocal:=ordinaryVortexBufferedVertices Q (i+1) 2;let Wlocal:=ordinaryVortexBufferedHubs Q (i+1) 2
    let Hlocal:=fun v u=>Hs (f v) (g u);
    ∀v,v∉Tlocal→|(((G.comap f).neighborFinset v∩Tlocal).card:ℝ)-2*(Wlocal.filter (Hlocal v)).card|≤
      (initialIndexDensity U D*pH)*β*Tlocal.card+εR*Tlocal.card+2*(εH*Wlocal.card)+
        3*(2*((3*d:ℕ):ℝ))+2*deepCost i:=by
  intro F R J S H S₀ H₀ X T Z W hist hstate f g Tlocal Wlocal Hlocal
  let b:ℝ:=(initialIndexDensity U D*pH)*β*Tlocal.card+εR*Tlocal.card+2*(εH*Wlocal.card)+3*(2*((3*d:ℕ):ℝ))
  let Rref:=(R\F)\(⊥:SimpleGraph V)
  let Jref:=fun v u=>J v u∧¬False
  let Ref0:=Rref\ordinaryResourceRim Rref K
  let Href0:=fun v u=>Jref v u∧¬(Sum.inr (v,u)∈K)
  have hlocal:=ordinary_vortex_initial_deep_sample_balance P ⊥ (fun _ _=>False) D m β ε pR pH εR εH Q π hπ d s j σ K
    hn hreg hρ hβ hpH hεR hεH hpR (by simp) (by simp) havoid hgood i hi
  have hI:Q.extendedVertices (i+1+2)⊆Q.extendedVertices (i+1):=Q.extendedVertices_subset (by omega)
  have hJ:Q.extendedIndices (i+1+2)⊆Q.extendedIndices (i+1):=Q.extendedIndices_subset (by omega)
  have hlocal':let Ilocal:Finset (Q.extendedVertices (i+1)):=Finset.univ.filter (fun x=>x.val∈Q.extendedVertices (i+1+2));
      let Jlocal:Finset (Q.extendedIndices (i+1)):=Finset.univ.filter (fun u=>u.val∈Q.extendedIndices (i+1+2));
      ∀v,v∉Ilocal→|((((Ref0.induce ((Q.extendedVertices (i+1)):Set V)).neighborFinset v)∩Ilocal).card:ℝ)-
        2*(Jlocal.filter (fun u=>Href0 v.val u.val)).card|≤b:=by
    intro Ilocal Jlocal v hv
    convert hlocal v using 1 <;> congr! 10 <;> first | exact Subsingleton.elim _ _ | simp [Href0,Jref,J]
  have hRef:=ordinary_cross_balance_induced_reverse Ref0 Href0 (Q.extendedVertices (i+1)) (Q.extendedVertices (i+1+2))
    (Q.extendedIndices (i+1)) (Q.extendedIndices (i+1+2)) hI hJ b
    (by intro Ilocal Jlocal v hv;convert hlocal' v hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  have hr:∀v∈Q.extendedVertices 1,∀w∈Q.extendedVertices 1,Rref.Adj v w↔Gbase.Adj v w:=by
    intro v hv w hw
    simpa [Rref,R,F,SimpleGraph.sdiff_adj] using hPairRim v hv w hw
  have hs:∀v∈Q.extendedVertices 1,∀u∈Q.extendedIndices 1,Jref v u↔Hbase v u:=by
    intro v hv u hu
    simpa [Jref,J] using hPairSpoke v hv u hu
  have hpairs:=ordinary_protected_pair_reserve_agreement Rref Gbase Jref Hbase K
    (Q.extendedVertices 1) (Q.extendedIndices 1) hr hs havoid
  have hparent:Q.extendedVertices (i+1)⊆Q.extendedVertices 1:=Q.extendedVertices_subset (by omega)
  have hhubs:Q.extendedIndices (i+1+2)⊆Q.extendedIndices 1:=Q.extendedIndices_subset (by omega)
  have hagree:=ordinary_protected_pair_balance_agreement Ref0 S₀ Href0 H₀ (Q.extendedVertices 1)
    (Q.extendedVertices (i+1)) (Q.extendedVertices (i+1+2)) (Q.extendedIndices 1) (Q.extendedIndices (i+1+2))
    hparent hI hhubs hpairs.1 hpairs.2
  have hinit:∀v∈Q.extendedVertices (i+1),v∉Q.extendedVertices (i+1+2)→
      |((S₀.neighborFinset v∩Q.extendedVertices (i+1+2)).card:ℝ)-
        2*((Q.extendedIndices (i+1+2)).filter (H₀ v)).card|≤b:=by
    intro v hv hv'
    have hnei:=hagree.2.1 v hv
    have hrow:=hagree.2.2.1 v hv
    have hneicard:((Ref0.neighborFinset v∩Q.extendedVertices (i+1+2)).card:ℝ)=
        ((S₀.neighborFinset v∩Q.extendedVertices (i+1+2)).card:ℝ):=by
      have hh:=congrArg (fun X:Finset V=>(X.card:ℝ)) hnei
      convert hh using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
    have hrowcard:(((Q.extendedIndices (i+1+2)).filter (Href0 v)).card:ℝ)=
        (((Q.extendedIndices (i+1+2)).filter (H₀ v)).card:ℝ):=by
      have hh:=congrArg (fun X:Finset U=>(X.card:ℝ)) hrow
      convert hh using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
    have hh:|((Ref0.neighborFinset v∩Q.extendedVertices (i+1+2)).card:ℝ)-
        2*((Q.extendedIndices (i+1+2)).filter (Href0 v)).card|≤b:=by
      convert hRef v hv hv' using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
    rw [hneicard,hrowcard] at hh
    convert hh using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  have hnow:=ordinary_vortex_uniform_history_deep_target_cross P S₀ G H₀ Hs D m β ε Q r 2 i L (by omega)
    cost deepCost A inner cross b hist hiL hstate
    (by intro v hv hv';convert hinit v hv hv' using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  have hsum:(∑t∈Finset.range (i+1),if t∈Finset.Icc (i+2-2) i then 2*deepCost t else 0)=2*deepCost i:=by
    simp
  intro v hv
  have hh:=hnow v hv
  rw [hsum] at hh
  exact hh
end Oberwolfach
