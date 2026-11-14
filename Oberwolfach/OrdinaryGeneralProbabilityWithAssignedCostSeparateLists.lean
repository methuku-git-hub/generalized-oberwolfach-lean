module

public import Oberwolfach.OrdinaryOriginalGeneralProbabilityFromSameSampleEventSeparateLists
public import Oberwolfach.OrdinaryTriangleAssignedUniformReservoirCostSeparateLists
public import Oberwolfach.OrdinaryInitialConflictBudgetEventually

@[expose] public section
/-! Transfer the matching/correction prior and its same-sample wheel tests
together to the original retention law, without an additional failure loss. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option maxRecDepth 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_general_probability_with_assigned_cost_separate_lists
    (rstar m k d K:ℕ) (hd:2≤d) (hrstar:0<rstar) (βfreq ρ₀ α θhost ε βv:ℝ)
    (δ θ aRow γrow σbal lamMatch lamPlace ξedit bMatch rate ξroot:ℝ)
    (mAbs tAbs aAbs bAbs:ℕ)
    (Nplace dNeed:ℕ) (η capEdit αplace ζPlace κ b z matchErr κprime ζret:ℝ)
    (hm:7≤m) (hK:0<K) (hda:1/θ≤d) (hη:0<η) (hcap:capEdit≤η)
    (hstage:OrdinaryPlacementStage m dNeed αplace lamPlace ζPlace capEdit δ θ κ b z matchErr σbal κprime)
    (hafter:OrdinaryPlacementAfterSpacing m d Nplace αplace δ θ κ b z matchErr ζret)
    (hmatching:OrdinaryPlacementMatchingRateBounds K θ κprime b z δ matchErr lamMatch aRow γrow)
    (hξ:0≤ξedit) (hξσ:ξedit≤σbal) (hρ:0<ρ₀) (hα:0<α) (hθhost:1/2≤θhost) (hβfreq:0<βfreq)
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
      (Tests:(Σσ:∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e,R σ)×(Sym2 (Fin n)→Bool)→Prop)
      (bprob:ℝ),
    let p:=initialIndexDensity (Fin qCount) D*rsv/2
    let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ ((m:ℝ)+1) D
    let marks:=ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1)
    let spokes:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ ((m:ℝ)+1)
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p 0 p₂ 0 sampling.u
      sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum d hd marks sampling.hq sampling.hQ spokes sampling.hs sampling.hS);
    let E:=OrdinaryAssignedCorrectionEvent rstar d mAbs aAbs bAbs tAbs q₀ n qCount K D hd (θ/2) χlocal χglobal χhub χcol ξabs
      P (permutationConflictGraph π (3*d)) π F hF i₀ rsv θ ρ₀ (βfreq/200) m sampling
      (Finset.univ\Q.extendedVertices 1) (Q.extendedVertices 1) (Q.extendedVertices Q.length)
      (Q.extendedIndices Q.length) (Q.extendedIndices 1) (Q.extendedIndices 1) R ν
      ζevent χpair χlist χbal χbd χnbr χpairR χpath Cres lamMatch aRow γrow σbal aEvent ζDel lamSel bMatch w seed tMatch ξMatch;
    bprob≤((μ.sigma ν).prod κcoin).probability (fun z=>E z∧Tests z)→
    2*mv≤mAbs→
    (∀z,E z→Tests z→
      (∀Kres JQ JH,
        let raw:=fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)
        let Bad:=permutationConflictGraph π (3*d)
        let Reference:=rawWheelGraph P raw\Bad
        let Href:=rawWheelSpokes π d raw false;
        OrdinaryCorrectedProtectedReservoirWitness rstar mAbs tAbs aAbs bAbs ξabs Reference Bad Href
          (Finset.univ\Q.extendedVertices 1) (Q.extendedVertices 1) (Q.extendedVertices Q.length)
          (Q.extendedIndices Q.length) (Q.extendedIndices 1) Kres JQ JH→
        let cost:=ordinaryTriangleAssignedReservoirCost d δ aRow γrow ξedit σbal sampling.u Kres;
        0≤cost ∧ cost≤14*η*n ∧ cost+2*((3*d:ℕ):ℝ)≤15*η*n)→
      OrdinaryGeneralUniformMatchedWheelOutcome (mAbs:=mAbs) (tAbs:=tAbs) (aAbs:=aAbs) (bAbs:=bAbs)
        rstar d P D mv βv ε rate ξroot Q π F Cres (Finset.univ\Q.extendedVertices 1)
        (Q.extendedVertices Q.length) (Q.extendedIndices Q.length) ξabs
        (ordinaryTriangleAssignedReservoirCost d δ aRow γrow ξedit σbal sampling.u) z.1.1)→
    let aBound:=2^(tAbs*tAbs)*aAbs;let bBound:=2^(tAbs*tAbs)*bAbs;
    bprob≤(FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin (initialIndexDensity (Fin qCount) D)
      (by unfold initialIndexDensity;positivity)
      (by rw [←sampling.hphysical];exact sampling.hsum))).probability
      (fun σ=>ProtectedFactorPreparation P (retainedGraph P σ) (Q.extendedVertices 1) ξedit (aBound*aBound+aBound*bBound) F)
 :=by
  obtain ⟨Nmatch,hmatch⟩:=ordinary_initial_conflict_budget_eventually d η hη
  obtain ⟨Ncost,_,hcost⟩:=ordinary_triangle_assigned_uniform_reservoir_cost_separate_lists m d tAbs aAbs bAbs K Nplace dNeed
    η capEdit αplace lamPlace ζPlace δ θ κ b z matchErr σbal κprime ζret lamMatch aRow γrow ξedit
    hm hd hK hda hη hcap hstage hafter hmatching hξ hξσ Nmatch hmatch
  obtain ⟨Nterminal,hN⟩:=ordinary_original_general_probability_from_same_sample_event_separate_lists rstar m k d K hd hrstar βfreq ρ₀ α θhost ε βv
    δ θ aRow γrow σbal lamMatch lamPlace ξedit bMatch rate ξroot mAbs tAbs aAbs bAbs hterminal
  refine ⟨max 2 (max Ncost Nterminal),?_⟩
  intro n qCount D hn hq F hF Allowed hAllowed P hreg hdegree hρlo hρhi mv Q π hnoshort
    i₀ rsv Cres sampling w seed τ tMatch ξMatch ζSel lamSel ζDel ζevent χpair χlist χbal χbd χnbr χpairR χpath aEvent BO hwitness
    q₀ χlocal χglobal χhub χcol ξabs R _ ν κcoin Tests bprob p p₂ marks spokes μ E hprob hAbs hSplit aBound bBound
  have hn0:0<n:=by omega
  have hD:0<D:=by
    have hnreal:0<(n:ℝ):=by exact_mod_cast hn0
    have hpositive:0<θhost+α:=by linarith
    have hprod:0<(θhost+α)*(n:ℝ):=mul_pos hpositive hnreal
    have :0<(D:ℝ):=lt_of_lt_of_le hprod hdegree
    exact_mod_cast this
  apply hN n qCount D (by omega) hq F hF Allowed hAllowed P hreg hdegree hρlo hρhi mv Q π hnoshort
    i₀ rsv Cres sampling w seed τ tMatch ξMatch ζSel lamSel ζDel ζevent χpair χlist χbal χbd χnbr χpairR χpath aEvent BO hwitness
    q₀ χlocal χglobal χhub χcol ξabs R ν κcoin Tests bprob hprob hAbs
  intro z hz hTests
  apply hSplit z hz hTests
  intro Kres JQ JH raw Bad Reference Href hw cost
  exact hcost n (by omega) hn0 D qCount hD F hF Allowed hAllowed i₀ rsv ρ₀ (βfreq/200) (by positivity) (by positivity)
    hρlo hρhi sampling rstar k P π Cres w seed lamSel τ tMatch ξMatch bMatch ζDel ζevent χpair χlist χbal χbd χnbr χpairR χpath aEvent α BO hwitness
    rstar mAbs ξabs (Finset.univ\Q.extendedVertices 1) (Q.extendedVertices 1) (Q.extendedVertices Q.length)
    (Q.extendedIndices Q.length) (Q.extendedIndices 1) z.1.1 Kres JQ JH hw
end Oberwolfach
