module

public import Oberwolfach.OrdinaryOriginalCommonEventConditionalTransferSeparateLists

@[expose] public section
/-! A common event carrying correction and uniform split certificates
transfers directly to the original retention-law preparation probability. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 70000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 65536
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_original_uniform_split_probability_separate_lists
    (rstar m k d K:ℕ) (hd:2≤d) (βfreq ρ₀ α θhost ε βv:ℝ)
    (δ θ aRow γrow σbal lamMatch lamPlace ξedit bMatch rate ξroot:ℝ)
    (mAbs tAbs aAbs bAbs:ℕ)
    (hrstar:0<rstar)
    (hterminal:OrdinaryOriginalTerminalConditionalPreparationSeparateListsAt rstar m k d K hd βfreq ρ₀ α θhost ε βv
      δ θ aRow γrow σbal lamMatch lamPlace ξedit bMatch rate ξroot mAbs tAbs aAbs bAbs) :
    ∃N:ℕ,∀n qCount D:ℕ,N≤ n→ qCount≤ n→
    ∀(F:Fin qCount→ SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
      (Allowed:Set ℕ),(∀u,AllowedCycleLengths (F u) Allowed)→
    ∀(P:SimpleGraph (Fin n)),P.IsRegularOfDegree D→(θhost+α)*(n:ℝ)≤ D→
      ρ₀≤ initialIndexDensity (Fin qCount) D→ initialIndexDensity (Fin qCount) D≤ 1→
    ∀(mv:ℕ) (Q:Vortex (Fin qCount) P D βv ε mv) (π:Equiv.Perm (Fin n)),
      (∀x l,0<l→ l<2*d+1→(π^l) x≠x)→
    ∀(i₀:Fin K) (rsv:ℝ) (Cres:∀u,Finset (F u).ConnectedComponent)
      (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ ((m:ℝ)+1) ρ₀ (βfreq/200) d)
      (w:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ ℝ)
      (seed:(Fin (m+1)→ Fin n)→ ℝ) (τ tMatch ξMatch ζSel lamSel ζDel ζevent χpair χlist χbal χbd χnbr χpairR χpath aEvent:ℝ)
      (BO:Fin K→ ℝ),
      OrdinaryOriginalSelectorFactorWitness n qCount D rstar m k d K hd ρ₀ θ lamMatch aRow γrow lamSel ζDel
        (βfreq/200) τ tMatch ξMatch bMatch σbal ζevent χpair χlist χbal χbd χnbr χpairR χpath aEvent α BO F hF P π i₀ rsv Cres sampling w seed→
    ∀(q₀:ℕ) (χlocal χglobal χhub χcol ξabs:ℝ)
      (R:(∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e)→Type)
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)) (κcoin:FiniteLaw (Sym2 (Fin n)→Bool))
      (Common:(Σσ:∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e,R σ)×(Sym2 (Fin n)→Bool)→Prop)
      (bprob:ℝ),
    let p:=initialIndexDensity (Fin qCount) D*rsv/2
    let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ ((m:ℝ)+1) D
    let marks:=ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1)
    let spokes:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ ((m:ℝ)+1)
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p 0 p₂ 0 sampling.u
      sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum d hd marks sampling.hq sampling.hQ spokes sampling.hs sampling.hS);
    bprob≤((μ.sigma ν).prod κcoin).probability Common→
    2*mv≤mAbs→
    (∀z,Common z→
    OrdinaryAssignedCorrectionEvent rstar d mAbs aAbs bAbs tAbs q₀ n qCount K D hd (θ/2) χlocal χglobal χhub χcol ξabs
      P (permutationConflictGraph π (3*d)) π F hF i₀ rsv θ ρ₀ (βfreq/200) m sampling
      (Finset.univ\Q.extendedVertices 1) (Q.extendedVertices 1) (Q.extendedVertices Q.length)
      (Q.extendedIndices Q.length) (Q.extendedIndices 1) (Q.extendedIndices 1) R ν
      ζevent χpair χlist χbal χbd χnbr χpairR χpath Cres lamMatch aRow γrow σbal aEvent ζDel lamSel bMatch w seed tMatch ξMatch
      z ∧
    let σ:=z.1.1;
    let Inner:=Q.extendedVertices 1;let Hubs:=Q.extendedIndices 1;
    let Sample:=longPhysicalStateGraph P σ {0,1,2,3,4};let Bad:=permutationConflictGraph π (3*d);
    let raw:=fun e=>expandedOrdinarySelectedCollapse e (σ e);
    let RawReference:=rawWheelGraph P raw\Bad;let Ref:=longPhysicalStateGraph P σ {0}\Bad;
    let Href:=rawWheelSpokes π d raw false;
    let Changed:=fun S:SimpleGraph (Fin n)=>∀v,
      ((Finset.univ.filter (fun x=>Xor (S.Adj v x) (Sample.Adj v x))).card:ℝ)≤ ξedit*n;
    let edit:=ξedit*n;let LF:ℝ:=2*((3*d:ℕ):ℝ);let newLoss:=5*Real.sqrt δ*n;
    let κref:ℝ:=(max aRow γrow)*n+sampling.u*n+3*(n:ℝ)^(3/5:ℝ)+((6*d+4:ℕ):ℝ)+edit+LF;
    let Lrim:=edit+κref+newLoss;let e:=σbal*n+2*(σbal*n)+LF;
    let Lspoke:=max (2*newLoss+(Lrim+e)/2) (2*(δ*n)+σbal*n);
    (∀(Kabs:Finset (Sym2 (Fin n)⊕(Fin n×Fin qCount))) (JQ:SimpleGraph (Fin n)) (JH:Fin n→ Fin qCount→ Prop),
      OrdinaryCorrectedProtectedReservoirWitness rstar mAbs tAbs aAbs bAbs ξabs RawReference Bad Href
        (Finset.univ\Inner) Inner (Q.extendedVertices Q.length) (Q.extendedIndices Q.length) Hubs Kabs JQ JH →
      let editCost:=Lrim+Lspoke+(ordinaryResourceRows Kabs).card+(ordinaryResourceHubs Kabs).card;
      ∀S:SimpleGraph (Fin n),S≤ P→ S.IsRegularOfDegree (2*qCount)→
        ∀f:∀u,{x:Fin n // (F u).connectedComponentMk x∉Cres u}↪Fin n,
        OrdinaryTrackedComplementFor P S π d σ F Cres Inner Hubs Kabs editCost f→
        OrdinaryTrackedSplitWheelCertificatesAt P S Bad F Cres rstar Kabs D mv βv ε Q Q.length
          (ordinaryVortexSelectedCost Q rate) (ordinaryFineDeepCost Q ξroot) f))→
    let aBound:=2^(tAbs*tAbs)*aAbs;let bBound:=2^(tAbs*tAbs)*bAbs;
    bprob≤(FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin (initialIndexDensity (Fin qCount) D)
      (by unfold initialIndexDensity;positivity)
      (by rw [←sampling.hphysical];exact sampling.hsum))).probability
      (fun σ=>ProtectedFactorPreparation P (retainedGraph P σ) (Q.extendedVertices 1) ξedit (aBound*aBound+aBound*bBound) F)
 :=by
  obtain ⟨N,hN⟩:=ordinary_original_common_event_conditional_transfer_separate_lists rstar m k d K hd βfreq ρ₀ α θhost ε βv
    δ θ aRow γrow σbal lamMatch lamPlace ξedit bMatch rate ξroot mAbs tAbs aAbs bAbs hrstar hterminal
  refine ⟨N,?_⟩
  intro n qCount D hn hq F hF Allowed hAllowed P hreg hdegree hρlo hρhi mv Q π hnoshort
    i₀ rsv Cres sampling w seed τ tMatch ξMatch ζSel lamSel ζDel ζevent χpair χlist χbal χbd χnbr χpairR χpath aEvent BO hwitness
    q₀ χlocal χglobal χhub χcol ξabs R _ ν κcoin Common bprob p p₂ marks spokes μ hprob hAbs hcommon aBound bBound
  apply hN n qCount D hn hq F hF Allowed hAllowed P hreg hdegree hρlo hρhi mv Q π hnoshort
    i₀ rsv Cres sampling w seed τ tMatch ξMatch ζSel lamSel ζDel ζevent χpair χlist χbal χbd χnbr χpairR χpath aEvent BO hwitness
    q₀ χlocal χglobal χhub χcol ξabs R ν κcoin Common bprob hprob hAbs
  intro z hz
  obtain ⟨hEvent,hUniform⟩:=hcommon z hz
  refine ⟨hEvent,?_⟩
  intro σ Inner Hubs Sample Bad raw RawReference Ref Href Changed edit LF newLoss κref Lrim e Lspoke
  intro Kabs JQ JH hw editCost S hSP hS hContain hInner hChanged f hf
  exact hUniform Kabs JQ JH hw S hSP hS f hf
end Oberwolfach
