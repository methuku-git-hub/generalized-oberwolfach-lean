module

public import Oberwolfach.OrdinaryTriangleProbabilityWithDerivedLocalInputs
public import Oberwolfach.OrdinaryTriangleAssignedEndpointFailureBudget

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option maxRecDepth 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_high_probability_with_derived_inputs
    (m k d K:ℕ) (hd:2≤d) (βfreq ρ₀ α θhost ε βv:ℝ)
    (δ θ aRow γrow σbal lamMatch lamPlace ξedit bMatch rate ξroot:ℝ)
    (mAbs tAbs aAbs bAbs:ℕ)
    (Nplace dNeed N₀ M:ℕ) (hN₀:N₀≤M) (hε:0<ε) (hsize:2/ε≤(M:ℝ))
    (hβv0:0≤βv) (hβv1:βv≤1/4) (η capEdit αplace ζPlace κ b z matchErr κprime ζret:ℝ)
    (hm:7≤m) (hK:0<K) (hda:1/θ≤d) (hη:0<η) (hcap:capEdit≤η)
    (hstage:OrdinaryPlacementStage m dNeed αplace lamPlace ζPlace capEdit δ θ κ b z matchErr σbal κprime)
    (hafter:OrdinaryPlacementAfterSpacing m d Nplace αplace δ θ κ b z matchErr ζret)
    (hmatching:OrdinaryPlacementMatchingRateBounds K θ κprime b z δ matchErr lamMatch aRow γrow)
    (hξ:0≤ξedit) (hξσ:ξedit≤σbal) (hρ:0<ρ₀) (hα:0<α) (hθhost:1/2≤θhost) (hβfreq:0<βfreq)
    (hterminal:OrdinaryOriginalTerminalConditionalPreparationAt 3 m k d K hd βfreq ρ₀ α θhost ε βv
      δ θ aRow γrow σbal lamMatch lamPlace ξedit bMatch rate ξroot mAbs tAbs aAbs bAbs)
    (χ:ℝ) (hχ:0<χ) :
    ∃capFailure:ℝ,0<capFailure ∧ ∃N:ℕ,∀n qCount D:ℕ,N≤ n→ qCount≤ n→
    ∀(F:Fin qCount→ SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2),
      (∀u,βfreq*n≤((Finset.univ.filter (fun v=>Fintype.card ((F u).connectedComponentMk v)=3)).card:ℝ))→
      (∀u v,cycleThreshold (Fintype.card ((F u).connectedComponentMk v))≤θhost)→
      ∀(Allowed:Set ℕ),(∀u,AllowedCycleLengths (F u) Allowed)→
    ∀(P:SimpleGraph (Fin n)),P.IsRegularOfDegree D→(θhost+α)*(n:ℝ)≤ D→
      ρ₀≤ initialIndexDensity (Fin qCount) D→ initialIndexDensity (Fin qCount) D≤ 1→
    ∀(mv:ℕ) (Q:Vortex (Fin qCount) P D βv ε mv) (π:Equiv.Perm (Fin n)),
      (∀x l,0<l→ l<2*d+1→(π^l) x≠x)→0<mv→(M:ℝ)≤ε*mv/2→
    ∀(i₀:Fin K) (rsv:ℝ) (Cres:∀u,Finset (F u).ConnectedComponent)
      (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ ((m:ℝ)+1) ρ₀ (βfreq/200) d)
      (w:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ ℝ)
      (seed:(Fin (m+1)→ Fin n)→ ℝ) (τ tMatch ξMatch ζSel lamSel ζDel ζevent χpair χlist χbal χbd χnbr χpairR χpath aEvent:ℝ)
      (BO:Fin K→ ℝ),
      OrdinaryOriginalSelectorFactorWitness n qCount D 3 m k d K hd ρ₀ θ lamMatch aRow γrow lamPlace ζDel
        (βfreq/200) τ tMatch ξMatch bMatch σbal ζevent χpair χlist χbal χbd χnbr χpairR χpath aEvent α BO F hF P π i₀ rsv Cres sampling w seed→
    ∀(χlocal χglobal χhub χcol ξabs χinner χdeep χone χtwo χcut χhost χref χHub χendpoint:ℝ)
      (R:(∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e)→Type)
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)) (κcoin:FiniteLaw (Sym2 (Fin n)→Bool))
      (Tests:(Σσ:∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e,R σ)×(Sym2 (Fin n)→Bool)→Prop)
      ,
    let p:=initialIndexDensity (Fin qCount) D*rsv/2
    let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ ((m:ℝ)+1) D
    let marks:=ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1)
    let spokes:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ ((m:ℝ)+1)
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p 0 p₂ 0 sampling.u
      sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum d hd marks sampling.hq sampling.hQ spokes sampling.hs sampling.hS);
    let E:=OrdinaryAssignedCorrectionEvent 3 d mAbs aAbs bAbs tAbs 10 n qCount K D hd (θ/2) χlocal χglobal χhub χcol ξabs
      P (permutationConflictGraph π (3*d)) π F hF i₀ rsv θ ρ₀ (βfreq/200) m sampling
      (Finset.univ\Q.extendedVertices 1) (Q.extendedVertices 1) (Q.extendedVertices Q.length)
      (Q.extendedIndices Q.length) (Q.extendedIndices 1) (Q.extendedIndices 1) R ν
      ζevent χpair χlist χbal χbd χnbr χpairR χpath Cres lamMatch aRow γrow σbal aEvent ζDel lamPlace bMatch w seed tMatch ξMatch;
    ζevent≤capFailure→χpair≤capFailure→χlist≤capFailure→χbal≤capFailure→χbd≤capFailure→
    χnbr≤capFailure→χpairR≤capFailure→χpath≤capFailure→χcol≤capFailure→χhub≤capFailure→
    χglobal≤capFailure→χlocal≤capFailure→χinner≤capFailure→χdeep≤capFailure→
    χone≤capFailure→χtwo≤capFailure→χcut≤capFailure→χhost≤capFailure→χref≤capFailure→
    χHub≤capFailure→χendpoint≤capFailure→
    let loss0:=(((((((0+3*ζevent+χpair)+2*χlist)+χbal)+χbd)+χnbr)+χpairR)+χpath)
    let loss:=loss0+χcol+χhub+χglobal+2/(n:ℝ)^10+(1/(n:ℝ)+2/(n:ℝ)^2)+χlocal;
    1-(loss+χdeep+χone+χtwo+χcut+χHub+χhost+χref)-χinner-χendpoint≤
      ((μ.sigma ν).prod κcoin).probability (fun z=>E z∧Tests z)→
    2*mv≤mAbs→
    (∀z,E z→Tests z→
      (∀u (c:↥(Cres u)),Fintype.card c.val=2+1)→
      cycleThreshold 3≤θhost→
      (∀i,i<Q.length→N₀≤Fintype.card (markedVortexVertexType Q i))→
      (∀Kres JQ JH,
        let raw:=fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)
        let Bad:=permutationConflictGraph π (3*d)
        let Reference:=rawWheelGraph P raw\Bad
        let Href:=rawWheelSpokes π d raw false;
        OrdinaryCorrectedProtectedReservoirWitness 3 mAbs tAbs aAbs bAbs ξabs Reference Bad Href
          (Finset.univ\Q.extendedVertices 1) (Q.extendedVertices 1) (Q.extendedVertices Q.length)
          (Q.extendedIndices Q.length) (Q.extendedIndices 1) Kres JQ JH→
        let cost:=ordinaryTriangleAssignedReservoirCost d δ aRow γrow ξedit σbal sampling.u Kres;
        0≤cost ∧ cost≤14*η*n ∧ cost+2*((3*d:ℕ):ℝ)≤15*η*n)→
      OrdinaryTriangleUniformMatchedWheelOutcome (mAbs:=mAbs) (tAbs:=tAbs) (aAbs:=aAbs) (bAbs:=bAbs)
        d P D mv βv ε rate ξroot Q π F Cres (Finset.univ\Q.extendedVertices 1)
        (Q.extendedVertices Q.length) (Q.extendedIndices Q.length) ξabs
        (ordinaryTriangleAssignedReservoirCost d δ aRow γrow ξedit σbal sampling.u) z.1.1)→
    let aBound:=2^(tAbs*tAbs)*aAbs;let bBound:=2^(tAbs*tAbs)*bAbs;
    1-χ-1/(n:ℝ)^10≤(FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin (initialIndexDensity (Fin qCount) D)
      (by unfold initialIndexDensity;positivity)
      (by rw [←sampling.hphysical];exact sampling.hsum))).probability
      (fun σ=>ProtectedFactorPreparation P (retainedGraph P σ) (Q.extendedVertices 1) ξedit (aBound*aBound+aBound*bBound) F)
 :=by
  obtain ⟨capFailure,hcapFailure,Nfailure,_,hfailure⟩:=ordinary_triangle_assigned_endpoint_failure_budget χ hχ
  obtain ⟨N,hN⟩:=ordinary_triangle_probability_with_derived_local_inputs m k d K hd βfreq ρ₀ α θhost ε βv
    δ θ aRow γrow σbal lamMatch lamPlace ξedit bMatch rate ξroot mAbs tAbs aAbs bAbs
    Nplace dNeed N₀ M hN₀ hε hsize hβv0 hβv1 η capEdit αplace ζPlace κ b z matchErr κprime ζret
    hm hK hda hη hcap hstage hafter hmatching hξ hξσ hρ hα hθhost hβfreq hterminal
  refine ⟨capFailure,hcapFailure,max Nfailure N,?_⟩
  intro n qCount D hn hq F hF habundance hthreshold Allowed hAllowed P hreg hdegree hρlo hρhi mv Q π hnoshort hmv hterminalSize
    i₀ rsv Cres sampling w seed τ tMatch ξMatch ζSel lamSel ζDel ζevent χpair χlist χbal χbd χnbr χpairR χpath aEvent BO hwitness
    χlocal χglobal χhub χcol ξabs χinner χdeep χone χtwo χcut χhost χref χHub χendpoint R _ ν κcoin Tests
    p p₂ marks spokes μ E hζ hp hl hb hbd hnbr hpR hpath hcol hhub hglobal hlocal
    hi hd' h1 h2 hc hhost href hHub hend loss0 loss hprob hAbs hSplit aBound bBound
  have hprob':1-χ-1/(n:ℝ)^10≤((μ.sigma ν).prod κcoin).probability (fun z=>E z∧Tests z):=by
    apply hfailure n (by omega) ζevent χpair χlist χbal χbd χnbr χpairR χpath χcol χhub χglobal χlocal
      hζ hp hl hb hbd hnbr hpR hpath hcol hhub hglobal hlocal
      χinner χdeep χone χtwo χcut χhost χref χHub χendpoint hi hd' h1 h2 hc hhost href hHub hend
      _ ((μ.sigma ν).prod κcoin) (fun z=>E z∧Tests z)
    exact hprob
  exact hN n qCount D (by omega) hq F hF habundance hthreshold Allowed hAllowed P hreg hdegree hρlo hρhi mv Q π hnoshort hmv hterminalSize
    i₀ rsv Cres sampling w seed τ tMatch ξMatch ζSel lamSel ζDel ζevent χpair χlist χbal χbd χnbr χpairR χpath aEvent BO hwitness
    10 χlocal χglobal χhub χcol ξabs R ν κcoin Tests (1-χ-1/(n:ℝ)^10) hprob' hAbs hSplit
end Oberwolfach
