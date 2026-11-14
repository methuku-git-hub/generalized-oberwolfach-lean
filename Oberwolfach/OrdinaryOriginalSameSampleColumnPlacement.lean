module

public import Oberwolfach.OrdinaryAssignedSameSampleColumnPlacement
public import Oberwolfach.OrdinarySelectorPlacementFactorInputs
public import Oberwolfach.OrdinarySelectedPlacementConcreteBudgets
public import Oberwolfach.OrdinaryEarlyScaleLePlacementCapacity
public import Oberwolfach.OrdinaryPlacementLargeOrderBudgets
public import Oberwolfach.OrdinaryAssignedReservoirRateInputs
public import Oberwolfach.MarkedInitialInnerVertexBound

@[expose] public section
/-! The original factor selector, regular host and selected placement scales
supply the deterministic inputs to the same-sample column matching theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 65536
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance 100000] Finset.decidableDforallFinset

theorem ordinary_original_same_sample_column_placement
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
      OrdinaryOriginalSelectorFactorWitness n qCount D rstar m k d K hd ρ₀ θ lamMatch aRow γrow lamPlace ζDel
        (βfreq/200) τ tMatch ξMatch bMatch σbal ζevent χpair χlist χbal χbd χnbr χpairR χpath aEvent α BO F hF P π i₀ rsv Cres sampling w seed→
    ∀(σ:∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e)
      (q₀:ℕ) (χlocal χglobal χhub χcol ξabs:ℝ)
      (R:(∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e)→ Type)
      [∀σ,Fintype (R σ)] (ρ:∀σ,FiniteLaw (R σ)) (extra:R σ) (coins:Sym2 (Fin n)→ Bool),
    OrdinaryAssignedCorrectionEvent rstar d mAbs aAbs bAbs tAbs q₀ n qCount K D hd (θ/2) χlocal χglobal χhub χcol ξabs
      P (permutationConflictGraph π (3*d)) π F hF i₀ rsv θ ρ₀ (βfreq/200) m sampling
      (Finset.univ\Q.extendedVertices 1) (Q.extendedVertices 1) (Q.extendedVertices Q.length)
      (Q.extendedIndices Q.length) (Q.extendedIndices 1) (Q.extendedIndices 1) R ρ
      ζevent χpair χlist χbal χbd χnbr χpairR χpath Cres lamMatch aRow γrow σbal aEvent ζDel lamPlace bMatch w seed tMatch ξMatch
      (⟨σ,extra⟩,coins)→
    let Inner:=Q.extendedVertices 1;let Hubs:=Q.extendedIndices 1;
    let Sample:=longPhysicalStateGraph P σ {0,1,2,3,4};let Bad:=permutationConflictGraph π (3*d);
    let RawReference:=rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (σ e))\Bad;
    let Href:=rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (σ e)) false;
    let Ref:=longPhysicalStateGraph P σ {0}\Bad;
    let J:=ordinaryEmptyRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false);
    ∃(Kabs:Finset (Sym2 (Fin n)⊕(Fin n×Fin qCount))) (JQ:SimpleGraph (Fin n)) (JH:Fin n→ Fin qCount→ Prop),
      OrdinaryCorrectedProtectedReservoirWitness rstar mAbs tAbs aAbs bAbs ξabs RawReference Bad Href
        (Finset.univ\Inner) Inner (Q.extendedVertices Q.length) (Q.extendedIndices Q.length) Hubs Kabs JQ JH ∧
      ∀S:SimpleGraph (Fin n),
        (∀v,((Finset.univ.filter (fun x=>Xor (S.Adj v x) (Sample.Adj v x))).card:ℝ)≤ ξedit*n)→
        OrdinarySelectedPostmatchingEmbeddingTrackedResult F hF Cres i₀ rsv θ lamMatch aRow γrow m d π P
          (Sample\S) S (ordinaryMatchingProtect Ref Inner Kabs) Sample Ref Bad σ 0 J Inner Hubs
          (ordinaryReservoirSpokeLabels Kabs) δ :=by
  let smin:ℝ:=βfreq/200
  let αcap:ℝ:=5*ρ₀*smin^2/128
  let cbudget:ℝ:=min (1/1024:ℝ) (min (αcap/4096) (1/2:ℝ)/8)
  have hsmin:0<smin:=by dsimp [smin];positivity
  have hαcap:0<αcap:=by dsimp [αcap];positivity
  obtain ⟨hδ,hδ1,hδlist,hθ,hθ1,hζret,hmatch0,hmatchUpper,hκ,hrate,hsizeBudget,hb,hcapacity,hbα,hbδ,hspace⟩:=
    ordinary_selected_placement_concrete_budgets m d K Nspace dNeed αcap lamPlace ζPlace capEdit δ θ κ b z matchErr σbal κ' ζret lamMatch aRow γrow hstage hafter hmatching
  have hEarlyKeep:=hEarly
  obtain ⟨hβPlace,hβPlace1,hlam,hζPlace,hlistBudget,_,_,_,_,_,_,_,_,hrates⟩:=hEarly
  have hlam1:lamPlace/2≤ 1:=by linarith
  obtain ⟨Nlist,hlist⟩:=hrates d hdMin
  obtain ⟨Nlarge,hlarge⟩:=ordinary_placement_large_order_budgets αcap lamPlace δ hαcap
  obtain ⟨Nplace,hplace⟩:=ordinary_assigned_same_sample_column_placement d m hm hd lamPlace ζPlace b εearly cbudget θ z aRow γrow (θ/2) bMatch αcap δ ζret κ ξedit
    hθ hθ1 hδ hlam hb hcolumns rstar mAbs tAbs aAbs bAbs
  refine ⟨max 2 (max Nspace (max Nlist (max Nlarge Nplace))),?_⟩
  intro n qCount D hn hq F hF Allowed hAllowed P hreg hdegree hρlo hρhi mv Q π hnoshort i₀ rsv Cres sampling w seed τ tMatch ξMatch ζSel lamSel ζDel ζevent χpair χlist χbal χbd χnbr χpairR χpath aEvent BO hwitness σ q₀ χlocal χglobal χhub χcol ξabs R _ ρ extra coins hEvent
  have hn2:2≤ n:=by omega
  have hn0:(0:ℝ)≤ n:=by positivity
  have hD:0<D:=by
    have hpos:(0:ℝ)<(θhost+α)*(n:ℝ):=by positivity
    exact_mod_cast (lt_of_lt_of_le hpos hdegree)
  have hDhalf:(1/2:ℝ)*(n:ℝ)≤ D:=by nlinarith [hdegree]
  have hP:∀x,(1/2+α/2)*n≤(P.degree x:ℝ):=by
    intro x
    rw [hreg x]
    nlinarith [hdegree]
  have hfactor:=ordinary_selector_placement_factor_inputs n qCount D rstar m k d K hd ρ₀ θ lamMatch aRow γrow lamPlace ζDel smin τ tMatch ξMatch bMatch σbal ζevent χpair χlist χbal χbd χnbr χpairR χpath aEvent α BO F hF P π i₀ rsv Cres sampling w seed hsmin hwitness
  obtain ⟨hrs0,hrs1,hsize,hres,hClass,hqprob⟩:=hfactor
  have hreserve:=ordinary_assigned_reservoir_rate_inputs F hF P hreg hD K i₀ rsv θ ((m:ℝ)+1) ρ₀ smin (ρ₀*smin/2) d hρ hρlo hDhalf (by positivity) (by linarith) sampling
  obtain ⟨hUlo,hp,hp2,hrsvlo,hrsOne,hpeq,hseq,hzeroProb⟩:=hreserve
  have hslo:smin≤ rsv:=hwitness.2.1
  have hsmall:=ordinary_early_scale_le_placement_capacity (α/2) ρ₀ smin capInner βPlace lamPlace ζPlace εearly ε dMin hρ hsmin hEarlyKeep hε.le hεearly
  obtain ⟨_,_,hHubs⟩:=hsmall
  have hInner:((Q.extendedVertices 1).card:ℝ)≤ εearly*n:=by
    have hh:=marked_initial_inner_vertex_bound Q hε.le
    simp only [Fintype.card_fin] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hεearly hn0)
  obtain ⟨hpow,hNβ,hNδ⟩:=hlarge n (by omega)
  obtain ⟨hDsmall,hNsmall,hRowRate⟩:=hspace n (by omega)
  obtain ⟨herror,hmargin,_⟩:=hlist n (by omega)
  have hUn:Fintype.card (Fin qCount)≤ n:=by simpa using hq
  have hHubs':((Q.extendedIndices 1).card:ℝ)≤ αcap*n:=hHubs P βv Q hq
  exact hplace n (by omega) hn2 qCount hq P P le_rfl π σ (Finset.univ\Q.extendedVertices 1)
    (Q.extendedVertices Q.length) (Q.extendedVertices 1) (Q.extendedIndices Q.length) (Q.extendedIndices 1) (Q.extendedIndices 1) ξabs
    (α/2) (ρ₀*smin/2) (initialIndexDensity (Fin qCount) D*rsv/2) smin rsv βPlace ζPlace
    (ordinaryAssignedSpokeProbability F hF K i₀ rsv θ ((m:ℝ)+1)) (by positivity) (by positivity) hp hsmin.le hslo
    hβPlace.le hζPlace.le (le_refl _) hP herror hmargin hlistBudget hInner F hF Cres i₀ lamMatch D ρ₀ sampling
    q₀ χlocal χglobal χhub χcol R ρ ζevent χpair χlist χbal χbd χnbr χpairR χpath σbal aEvent ζDel w seed tMatch ξMatch extra coins hEvent
    rfl rfl hK hD hrs0 hrs1 hρ hρlo hρhi Allowed hAllowed hClass hUn hsize hres hnoshort hζret.le hmatch0 hmatchUpper hκ hrate
    hsizeBudget hsmin hcapacity hUlo hHubs' hpow hbα hbδ hDsmall hNsmall hRowRate hlam1 hδlist hNβ hNδ
end Oberwolfach
