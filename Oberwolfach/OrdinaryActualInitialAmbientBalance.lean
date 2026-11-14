module

public import Oberwolfach.OrdinaryVortexInitialAmbientBalanceAt
public import Oberwolfach.OrdinaryProtectedPairReserveAgreement

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryVortexActualInitialAmbientBalanceAt
    (ε ρ₀ α pmin hmin η cBoundary δ:ℝ) (d:ℕ) (β:ℝ) (m₀:ℕ):Prop :=
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U] (P Gbase:SimpleGraph V) (Hbase:V→U→Prop) (D m:ℕ),
      P.IsRegularOfDegree D→0<Fintype.card V→(Fintype.card V:ℝ)/2≤D→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→m₀≤m→
    ∀(Q:Vortex U P D β ε m) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (pR pH θ εR εH βe βh:ℝ) (s:U→Color→ℝ) (j:Color)
      (σ:RawWheelOutcome V U Γ Color) (K:Finset (Sym2 V⊕(V×U))),
      pmin≤pR→pR≤1→hmin≤pH→1/2≤θ→(θ+α)*Fintype.card V≤D→
      0≤εR→εR≤δ→0≤εH→εH≤δ→0≤βe→βe≤cBoundary*ε→0≤βh→βh≤cBoundary*ε→
      pR=initialIndexDensity U D*pH→(∀u,s u j=pH)→
      (∀v∈Q.extendedVertices 1,∀w∈Q.extendedVertices 1,
        ((rawWheelGraph P σ)\permutationConflictGraph π (3*d)).Adj v w↔Gbase.Adj v w)→
      (∀v∈Q.extendedVertices 1,∀u∈Q.extendedIndices 1,
        rawWheelSpokes π d σ j v u↔Hbase v u)→
      Disjoint K (ordinaryRootResources (Q.extendedVertices 1) (Q.extendedIndices 1))→
      OrdinaryFixedVortexRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d)) D m β ε Q π hπ pR pH s j σ→
    let S:=Gbase;
    let S₀:=S\ordinaryResourceRim S K;
    let H₀:=fun v u=>Hbase v u∧¬(Sum.inr (v,u)∈K);
    ∀i:ℕ,i+1<Q.length→
    let I:=markedVortexInnerVertices Q (i+1);
    (∀v∈Q.extendedVertices (i+2),|((spanningRestriction S₀ (Q.extendedVertices (i+2))).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H₀ v u∧v∈Q.extendedVertices (i+2)∧u∈Q.extendedIndices (i+2))).card|≤η*I.card) ∧
    (∀v∈Q.extendedVertices (i+1),v∉Q.extendedVertices (i+2)→
      |((S₀.neighborFinset v∩Q.extendedVertices (i+2)).card:ℝ)-
        2*((Q.extendedIndices (i+2)).filter (H₀ v)).card|≤η*I.card)

theorem ordinary_initial_ambient_balance_actual_of_reference
    (ε ρ₀ α pmin hmin η cBoundary δ:ℝ) (d:ℕ) (β:ℝ) (m₀:ℕ)
    (hbig:OrdinaryVortexInitialAmbientBalanceAt ε ρ₀ α pmin hmin η cBoundary δ d β m₀):
    OrdinaryVortexActualInitialAmbientBalanceAt ε ρ₀ α pmin hmin η cBoundary δ d β m₀ :=by
  intro V U Γ Color _ _ _ _ _ _ P Gbase Hbase D m hreg hn hD hρlo hρhi hmm Q π hπ
    pR pH θ εR εH βe βh s j σ K hpR hpR1 hpH hθ hdegree hεR hεRδ hεH hεHδ
    hβe hβec hβh hβhc hpEq hs hPairRim hPairSpoke havoid hgood S S₀ H₀ i hi I
  let R:=(rawWheelGraph P σ\permutationConflictGraph π (3*d))\(⊥:SimpleGraph V)
  let J:=fun v u=>rawWheelSpokes π d σ j v u∧¬False
  let Ref:=R\ordinaryResourceRim R K
  let Href:=fun v u=>J v u∧¬(Sum.inr (v,u)∈K)
  have hRef:=hbig V U Γ Color P ⊥ (fun _ _=>False) D m hreg hn hD hρlo hρhi hmm Q π hπ
    pR pH θ εR εH βe βh s j σ K hpR hpR1 hpH hθ hdegree hεR hεRδ hεH hεHδ
    hβe hβec hβh hβhc hpEq hs (by simp) (by simp) havoid hgood i hi
  have hRef':
      (∀v∈Q.extendedVertices (i+2),|((spanningRestriction Ref (Q.extendedVertices (i+2))).degree v:ℝ)-
        2*(Finset.univ.filter (fun u=>Href v u∧v∈Q.extendedVertices (i+2)∧u∈Q.extendedIndices (i+2))).card|≤η*I.card) ∧
      (∀v∈Q.extendedVertices (i+1),v∉Q.extendedVertices (i+2)→
        |((Ref.neighborFinset v∩Q.extendedVertices (i+2)).card:ℝ)-
          2*((Q.extendedIndices (i+2)).filter (Href v)).card|≤η*I.card):=by
    convert hRef using 1 <;> congr! 10 <;> first | exact Subsingleton.elim _ _ | simp [Href,J]
  have hr:∀v∈Q.extendedVertices 1,∀w∈Q.extendedVertices 1,R.Adj v w↔Gbase.Adj v w:=by
    intro v hv w hw
    simpa [R,SimpleGraph.sdiff_adj] using hPairRim v hv w hw
  have hs':∀v∈Q.extendedVertices 1,∀u∈Q.extendedIndices 1,J v u↔Hbase v u:=by
    intro v hv u hu
    simpa [J] using hPairSpoke v hv u hu
  have hpairs:=ordinary_protected_pair_reserve_agreement R Gbase J Hbase K (Q.extendedVertices 1) (Q.extendedIndices 1)
    hr hs' havoid
  have hparent:Q.extendedVertices (i+1)⊆Q.extendedVertices 1:=Q.extendedVertices_subset (by omega)
  have hinner:Q.extendedVertices (i+2)⊆Q.extendedVertices (i+1):=Q.extendedVertices_subset (by omega)
  have hhubs:Q.extendedIndices (i+2)⊆Q.extendedIndices 1:=Q.extendedIndices_subset (by omega)
  have hagree:=ordinary_protected_pair_balance_agreement Ref S₀ Href H₀ (Q.extendedVertices 1)
    (Q.extendedVertices (i+1)) (Q.extendedVertices (i+2)) (Q.extendedIndices 1) (Q.extendedIndices (i+2))
    hparent hinner hhubs hpairs.1 hpairs.2
  constructor
  · intro v hv
    have hspan:=hagree.1
    have hrow:=hagree.2.2.2 v (hinner hv)
    have hh:=hRef'.1 v hv
    have hrowcard:((Finset.univ.filter (fun u=>Href v u∧v∈Q.extendedVertices (i+2)∧u∈Q.extendedIndices (i+2))).card:ℝ)=
        ((Finset.univ.filter (fun u=>H₀ v u∧v∈Q.extendedVertices (i+2)∧u∈Q.extendedIndices (i+2))).card:ℝ):=by
      have hh:=congrArg (fun X:Finset U=>(X.card:ℝ)) hrow
      convert hh using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
    rw [hspan] at hh
    rw [hrowcard] at hh
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro v hv hvout
    have hnei:=hagree.2.1 v hv
    have hrow:=hagree.2.2.1 v hv
    have hneicard:((Ref.neighborFinset v∩Q.extendedVertices (i+2)).card:ℝ)=
        ((S₀.neighborFinset v∩Q.extendedVertices (i+2)).card:ℝ):=by
      have hh:=congrArg (fun X:Finset V=>(X.card:ℝ)) hnei
      convert hh using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
    have hrowcard:(((Q.extendedIndices (i+2)).filter (Href v)).card:ℝ)=
        (((Q.extendedIndices (i+2)).filter (H₀ v)).card:ℝ):=by
      have hh:=congrArg (fun X:Finset U=>(X.card:ℝ)) hrow
      convert hh using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
    have hh:=hRef'.2 v hv hvout
    rw [hneicard,hrowcard] at hh
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
