module

public import Oberwolfach.OrdinaryOriginalTerminalConditionalPreparationSeparateLists

@[expose] public section
/-! Name the original-host same-sample preparation callback, conditional
only on the actual split wheel certificates and terminal support budget. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryOriginalTerminalConditionalPreparationSeparateListsAt
    (rstar m k d K:ℕ) (hd:2≤d) (βfreq ρ₀ α θhost ε βv:ℝ)
    (δ θ aRow γrow σbal lamMatch lamPlace ξedit bMatch rate ξroot:ℝ)
    (mAbs tAbs aAbs bAbs:ℕ):Prop :=
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
    ∀(σ:∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e)
      (q₀:ℕ) (χlocal χglobal χhub χcol ξabs:ℝ)
      (R:(∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e)→ Type)
      [∀σ,Fintype (R σ)] (ρ:∀σ,FiniteLaw (R σ)) (extra:R σ) (coins:Sym2 (Fin n)→ Bool),
    OrdinaryAssignedCorrectionEvent rstar d mAbs aAbs bAbs tAbs q₀ n qCount K D hd (θ/2) χlocal χglobal χhub χcol ξabs
      P (permutationConflictGraph π (3*d)) π F hF i₀ rsv θ ρ₀ (βfreq/200) m sampling
      (Finset.univ\Q.extendedVertices 1) (Q.extendedVertices 1) (Q.extendedVertices Q.length)
      (Q.extendedIndices Q.length) (Q.extendedIndices 1) (Q.extendedIndices 1) R ρ
      ζevent χpair χlist χbal χbd χnbr χpairR χpath Cres lamMatch aRow γrow σbal aEvent ζDel lamSel bMatch w seed tMatch ξMatch
      (⟨σ,extra⟩,coins)→
    2*mv≤mAbs →
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
      ∀S:SimpleGraph (Fin n),S≤ P→ S.IsRegularOfDegree (2*qCount)→ ordinaryResourceRim Ref Kabs≤ S→
        (∀v∈Inner,∀x∈Inner,S.Adj v x↔Sample.Adj v x)→ Changed S→
        ∀f:∀u,{x:Fin n // (F u).connectedComponentMk x∉Cres u}↪Fin n,
        OrdinaryTrackedComplementFor P S π d σ F Cres Inner Hubs Kabs editCost f→
        OrdinaryTrackedSplitWheelCertificatesAt P S Bad F Cres rstar Kabs D mv βv ε Q Q.length
          (ordinaryVortexSelectedCost Q rate) (ordinaryFineDeepCost Q ξroot) f)→
    let aBound:=2^(tAbs*tAbs)*aAbs;let bBound:=2^(tAbs*tAbs)*bAbs;
    OrdinaryNaturalPreparationCertificate (r:=rstar) P Sample Inner ξedit (aBound*aBound+aBound*bBound) F Cres
end Oberwolfach
