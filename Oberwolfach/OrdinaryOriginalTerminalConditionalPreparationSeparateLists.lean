module

public import Oberwolfach.OrdinaryOriginalSameSampleConditionalPreparationSeparateLists
public import Oberwolfach.OrdinaryVortexTerminalPreparationGeometry

@[expose] public section
/-! The actual terminal vortex sets supply the absorber geometry for the
conditional preparation, once the support budget covers their size. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 65536
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_original_terminal_conditional_preparation_separate_lists
    (rstar m k d K dMin dNeed Nspace:ℕ) (hm:7≤ m) (hd:2≤ d) (hK:0<K) (hdMin:dMin≤ d)
    (βfreq ρ₀ α θhost capInner βPlace lamPlace ζPlace εearly ε βv:ℝ)
    (hβ:0<βfreq) (hρ:0<ρ₀) (hα:0<α) (hθhost:(1/2:ℝ)≤ θhost)
    (hε:0<ε) (hεearly:ε≤ εearly)
    (hEarly:OrdinaryPlacementEarlyRateData (α/2) ρ₀ (βfreq/200) capInner βPlace lamPlace ζPlace εearly dMin)
    (capEdit δ θ κ b z matchErr σbal κ' ζret lamMatch aRow γrow ξedit bMatch:ℝ)
    (hstage:OrdinaryPlacementStage m dNeed (5*ρ₀*(βfreq/200)^2/128) lamPlace ζPlace capEdit δ θ κ b z matchErr σbal κ')
    (hafter:OrdinaryPlacementAfterSpacing m d Nspace (5*ρ₀*(βfreq/200)^2/128) δ θ κ b z matchErr ζret)
    (hmatching:OrdinaryPlacementMatchingRateBounds K θ κ' b z δ matchErr lamMatch aRow γrow)
    (hda:1/θ≤ d)
    (hcolumns:OrdinaryEarlyUniformColumnsAtRate d m lamPlace ζPlace b εearly
      (min (1/1024:ℝ) (min ((5*ρ₀*(βfreq/200)^2/128)/4096) (1/2:ℝ)/8))
      θ z δ aRow γrow (θ/2) bMatch (5*ρ₀*(βfreq/200)^2/128) ξedit)
    (hξedit:0<ξedit) (hr:0<rstar) (rate ξroot:ℝ) (hrate:0≤rate) (hξroot:0≤ξroot)
    (mAbs tAbs aAbs bAbs:ℕ):
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
    OrdinaryNaturalPreparationCertificate (r:=rstar) P Sample Inner ξedit (aBound*aBound+aBound*bBound) F Cres :=by
  obtain ⟨N,hN⟩:=ordinary_original_same_sample_conditional_preparation_separate_lists rstar m k d K dMin dNeed Nspace hm hd hK hdMin
    βfreq ρ₀ α θhost capInner βPlace lamPlace ζPlace εearly ε βv hβ hρ hα hθhost hε hεearly hEarly
    capEdit δ θ κ b z matchErr σbal κ' ζret lamMatch aRow γrow ξedit bMatch hstage hafter hmatching hda hcolumns
    hξedit hr rate ξroot hrate hξroot mAbs tAbs aAbs bAbs
  refine ⟨max N 2,?_⟩
  intro n qCount D hn hq F hF Allowed hAllowed P hreg hdegree hρlo hρhi mv Q π hnoshort i₀ rsv Cres sampling w seed τ tMatch ξMatch ζSel lamSel ζDel ζevent χpair χlist χbal χbd χnbr χpairR χpath aEvent BO hwitness σ q₀ χlocal χglobal χhub χcol ξabs R _ ρ extra coins hEvent hAbs
    Inner Hubs Sample Bad raw RawReference Ref Href Changed edit LF newLoss κref Lrim e Lspoke hsplit aBound bBound
  have hn0:0<n:=by omega
  have hD:0<D:=by
    have hpos:(0:ℝ)<(θhost+α)*(n:ℝ):=by positivity
    exact_mod_cast (lt_of_lt_of_le hpos hdegree)
  have hgeom:=ordinary_vortex_terminal_preparation_geometry P βv ε Q hn0 hreg hD hρhi hε.le hAbs
  exact hN n qCount D (by omega) hq F hF Allowed hAllowed P hreg hdegree hρlo hρhi mv Q π hnoshort
    i₀ rsv Cres sampling w seed τ tMatch ξMatch ζSel lamSel ζDel ζevent χpair χlist χbal χbd χnbr χpairR χpath aEvent BO hwitness
    σ q₀ χlocal χglobal χhub χcol ξabs R ρ extra coins hEvent hgeom.1 hgeom.2.1 hgeom.2.2 hsplit
end Oberwolfach
