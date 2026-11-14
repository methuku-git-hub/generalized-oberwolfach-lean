module

public import Oberwolfach.OrdinaryAssignedEventConditionalPreparation
public import Oberwolfach.OrdinarySharedSamplePhysicalInclusion

@[expose] public section
/-! Use the corrected reservoir chosen by the same-sample placement and
apply the split wheel certificates for that very tracked remainder. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 65536
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_placed_split_preparation
    (r d mAbs a b t q₀ n qCount K D:ℕ) (hd:2≤d)
    (ζlocal χlocal χglobal χhub χcol ξ:ℝ)
    (P Bad:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (F:Fin qCount→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (i₀:Fin K) (rsv θ ρ₀ smin:ℝ) (mMatch:ℕ)
    (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ ((mMatch:ℝ)+1) ρ₀ smin d)
    (A Z Wterm:Finset (Fin n)) (Bterm B Htest:Finset (Fin qCount))
    (R:(∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e)→Type)
    [∀σ,Fintype (R σ)] (ρ:∀σ,FiniteLaw (R σ))
    (ζ χpair χlist χbal χbd χnbr χpairR χpath:ℝ)
    (Cres:∀u,Finset (F u).ConnectedComponent)
    (lamMatch aRow γrow σbal aEvent ζDel lamList bMatch:ℝ)
    (w:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ℝ)
    (seed:(Fin (mMatch+1)→Fin n)→ℝ) (tMatch ξMatch:ℝ)
    (z:(Σσ:∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e,R σ)×(Sym2 (Fin n)→Bool))
    (hBad:Bad=permutationConflictGraph π (3*d))
    (hz:OrdinaryAssignedCorrectionEvent r d mAbs a b t q₀ n qCount K D hd ζlocal χlocal χglobal χhub χcol ξ P Bad π
      F hF i₀ rsv θ ρ₀ smin mMatch sampling A Z Wterm Bterm B Htest R ρ ζ χpair χlist χbal χbd χnbr χpairR χpath
      Cres lamMatch aRow γrow σbal aEvent ζDel lamList bMatch w seed tMatch ξMatch z)
    (Inner:Finset (Fin n)) (Hubs:Finset (Fin qCount)) (δPlace ξedit:ℝ)
    (hn:0<n) (hδ:0≤δPlace) (hξedit:0≤ξedit) (haRow:0≤aRow) (hγrow:0≤γrow)
    (hsize:∀u (c:↥(Cres u)),Fintype.card c.val=r)
    (hCard:∀u,((r:ℕ):ℝ)*(Cres u).card=rsv*n)
    (hr:0<r) (hAbsSize:Wterm.card+Bterm.card≤mAbs) (hWsub:Wterm⊆Inner) (hBsub:Bterm⊆Hubs)
    (mv:ℕ) (βv εv:ℝ) (Vor:Vortex (Fin qCount) P D βv εv mv)
    (L:ℕ) (hL:0<L) (rate ξroot:ℝ) (hrate:0≤rate) (hξroot:0≤ξroot)
    (hWterm:Vor.extendedVertices L=Wterm) (hBterm:Vor.extendedIndices L=Bterm):
    let σ:=z.1.1;let p:=initialIndexDensity (Fin qCount) D*rsv/2;
    let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ ((mMatch:ℝ)+1) D;
    let Sample:=longPhysicalStateGraph P σ {0,1,2,3,4};
    let Reference:=longPhysicalStateGraph P σ {0}\Bad;
    let raw:=fun e=>expandedOrdinarySelectedCollapse e (σ e);
    let RawReference:=rawWheelGraph P raw\Bad;
    let Href:=rawWheelSpokes π d raw false;
    let Protect:=ordinaryMatchingProtect Reference Inner;
    let J:=ordinaryEmptyRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false);
    let Changed:=fun S:SimpleGraph (Fin n)=>∀v,
      ((Finset.univ.filter (fun x=>Xor (S.Adj v x) (Sample.Adj v x))).card:ℝ)≤ξedit*n;
    let edit:=ξedit*n;let LF:ℝ:=2*((3*d:ℕ):ℝ);let newLoss:=5*Real.sqrt δPlace*n;
    let κref:ℝ:=(max aRow γrow)*n+sampling.u*n+3*(n:ℝ)^(3/5:ℝ)+((6*d+4:ℕ):ℝ)+edit+LF;
    let Lrim:=edit+κref+newLoss;let e:=σbal*n+2*(σbal*n)+LF;
    let Lspoke:=max (2*newLoss+(Lrim+e)/2) (2*(δPlace*n)+σbal*n);
    (∃(Kabs:Finset (Sym2 (Fin n)⊕(Fin n×Fin qCount))) (JQ:SimpleGraph (Fin n)) (JH:Fin n→ Fin qCount→ Prop),
      OrdinaryCorrectedProtectedReservoirWitness r mAbs t a b ξ RawReference Bad Href A Z Wterm Bterm B Kabs JQ JH ∧
      ∀S,Changed S→
        OrdinarySelectedPostmatchingEmbeddingTrackedResult F hF Cres i₀ rsv θ lamMatch aRow γrow mMatch d π P
          (Sample\S) S (Protect Kabs) Sample Reference Bad σ 0 J Inner Hubs (ordinaryReservoirSpokeLabels Kabs) δPlace)→
    (∀(Kabs:Finset (Sym2 (Fin n)⊕(Fin n×Fin qCount))) (JQ:SimpleGraph (Fin n)) (JH:Fin n→ Fin qCount→ Prop),
      OrdinaryCorrectedProtectedReservoirWitness r mAbs t a b ξ RawReference Bad Href A Z Wterm Bterm B Kabs JQ JH →
      let editCost:=Lrim+Lspoke+(ordinaryResourceRows Kabs).card+(ordinaryResourceHubs Kabs).card;
      ∀S:SimpleGraph (Fin n),S≤ P→ S.IsRegularOfDegree (2*qCount)→ ordinaryResourceRim Reference Kabs≤ S→
        (∀v∈Inner,∀x∈Inner,S.Adj v x↔Sample.Adj v x)→ Changed S→
        ∀f:∀u,{x:Fin n // (F u).connectedComponentMk x∉Cres u}↪Fin n,
        OrdinaryTrackedComplementFor P S π d σ F Cres Inner Hubs Kabs editCost f→
        OrdinaryTrackedSplitWheelCertificatesAt P S Bad F Cres r Kabs D mv βv εv Vor L
          (ordinaryVortexSelectedCost Vor rate) (ordinaryFineDeepCost Vor ξroot) f)→
    let aBound:=2^(t*t)*a;let bBound:=2^(t*t)*b;
    OrdinaryNaturalPreparationCertificate (r:=r) P Sample Inner ξedit (aBound*aBound+aBound*bBound) F Cres :=by
  intro σ p p₂ Sample Reference raw RawReference Href Protect J Changed edit LF newLoss κref Lrim e Lspoke hplaced hsplit aBound bBound
  obtain ⟨Kabs,JQ,JH,hw,hmatching⟩:=hplaced
  have hw':OrdinaryCorrectedProtectedReservoirWitness r mAbs t a b ξ Reference Bad Href A Z Wterm Bterm B Kabs JQ JH:=by
    dsimp [RawReference,Reference,raw] at hw ⊢
    rw [ordinary_shared_sample_reference_graph_eq_state_zero P σ] at hw
    exact hw
  have hh:=hsplit Kabs JQ JH hw
  have hresult:=ordinary_assigned_event_conditional_preparation r d mAbs a b t q₀ n qCount K D hd ζlocal χlocal χglobal χhub χcol ξ P Bad π
    F hF i₀ rsv θ ρ₀ smin mMatch sampling A Z Wterm Bterm B Htest R ρ ζ χpair χlist χbal χbd χnbr χpairR χpath
    Cres lamMatch aRow γrow σbal aEvent ζDel lamList bMatch w seed tMatch ξMatch z hBad hz
    Inner Hubs δPlace ξedit hn hδ hξedit haRow hγrow hsize hCard hr hAbsSize hWsub hBsub
    mv βv εv Vor L hL rate ξroot hrate hξroot hWterm hBterm
    (by exact ⟨Kabs,JQ,JH,hw',hmatching,hh⟩)
  exact hresult
end Oberwolfach
