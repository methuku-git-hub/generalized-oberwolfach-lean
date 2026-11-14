module

public import Oberwolfach.OrdinaryAssignedFactorSameSampleCost

@[expose] public section
/-! Name the actual edited-target cost and obtain its uniform bound from the
original assigned factor witness for every corrected reservoir. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def ordinaryTriangleAssignedReservoirCost {n qCount:ℕ} (d:ℕ) (δ a γ ξedit σ u:ℝ)
    (Kabs:Finset (Sym2 (Fin n)⊕(Fin n×Fin qCount))):ℝ :=
  let LF:ℝ:=2*((3*d:ℕ):ℝ);
  let edit:=ξedit*n;let t:ℝ:=(n:ℝ)^(3/5:ℝ);
  let newLoss:=5*Real.sqrt δ*n;
  let κref:ℝ:=(max a γ)*n+u*n+3*t+((6*d+4:ℕ):ℝ)+edit+LF;
  let e:ℝ:=σ*n+2*(σ*n)+LF;
  let Lrim:=edit+κref+newLoss;
  let Lspoke:=max (2*newLoss+(Lrim+e)/2) (2*(δ*n)+σ*n);
  Lrim+Lspoke+(ordinaryResourceRows Kabs).card+(ordinaryResourceHubs Kabs).card

theorem ordinary_triangle_assigned_uniform_reservoir_cost
    (m d tAbs aAbs bAbs K N dNeed:ℕ)
    (η capEdit α lamList ζList δ θ κ b z matchErr σ κ' ζret lam a γ ξedit:ℝ)
    (hm:7≤ m) (hd:2≤ d) (hK:0<K) (hda:1/θ≤ d)
    (hη:0<η) (hcap:capEdit≤ η)
    (hstage:OrdinaryPlacementStage m dNeed α lamList ζList capEdit δ θ κ b z matchErr σ κ')
    (hafter:OrdinaryPlacementAfterSpacing m d N α δ θ κ b z matchErr ζret)
    (hmatching:OrdinaryPlacementMatchingRateBounds K θ κ' b z δ matchErr lam a γ)
    (hξ:0≤ ξedit) (hξσ:ξedit≤ σ) (M:ℕ)
    (hmatch:∀n:ℕ,M≤n→∀cost:ℝ,cost≤14*η*n→cost+2*((3*d:ℕ):ℝ)≤15*η*n):
    ∃Ncost:ℕ,M≤Ncost ∧ ∀n:ℕ,Ncost≤ n→ 0<n→∀(D qCount:ℕ),0<D→
    ∀(F:Fin qCount→ SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
      (Allowed:Set ℕ),(∀w,AllowedCycleLengths (F w) Allowed)→
    ∀(i₀:Fin K) (rsv ρ₀ smin:ℝ),0<smin→0<ρ₀→
      ρ₀≤ initialIndexDensity (Fin qCount) D→ initialIndexDensity (Fin qCount) D≤ 1→
    ∀(sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ ((m:ℝ)+1) ρ₀ smin d)
      (rstar k:ℕ) (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
      (Cres:∀u,Finset (F u).ConnectedComponent)
      (w:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ℝ)
      (seed:(Fin (m+1)→Fin n)→ℝ)
      (τ tMatch ξMatch bMatch ζDel ζevent χpair χlist χbal χbd χnbr χpairR χpath aEvent αOriginal:ℝ) (BO:Fin K→ℝ),
    OrdinaryOriginalSelectorFactorWitness n qCount D rstar m k d K hd ρ₀ θ lam a γ lamList ζDel smin τ tMatch ξMatch bMatch σ ζevent χpair χlist χbal χbd χnbr χpairR χpath aEvent αOriginal BO F hF P π i₀ rsv Cres sampling w seed→
    ∀(r mAbs:ℕ) (ξabs:ℝ) (A Z Wterm:Finset (Fin n)) (Bterm B:Finset (Fin qCount))
      (σx:∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e),
    let raw:=fun e=>expandedOrdinarySelectedCollapse e (σx e)
    let Bad:=permutationConflictGraph π (3*d)
    let Reference:=rawWheelGraph P raw\Bad
    let Href:=rawWheelSpokes π d raw false;
    ∀(Kabs:Finset (Sym2 (Fin n)⊕(Fin n×Fin qCount))) (JQ:SimpleGraph (Fin n)) (JH:Fin n→ Fin qCount→ Prop),
    OrdinaryCorrectedProtectedReservoirWitness r mAbs tAbs aAbs bAbs ξabs Reference Bad Href A Z Wterm Bterm B Kabs JQ JH→
      let cost:=ordinaryTriangleAssignedReservoirCost d δ a γ ξedit σ sampling.u Kabs;
      0≤cost ∧ cost≤14*η*n ∧ cost+2*((3*d:ℕ):ℝ)≤15*η*n :=by
  obtain ⟨Ncost,hM,hcost⟩:=ordinary_assigned_factor_same_sample_cost m d tAbs aAbs bAbs K N dNeed
    η capEdit α lamList ζList δ θ κ b z matchErr σ κ' ζret lam a γ ξedit
    hm hd hK hda hη hcap hstage hafter hmatching hξ hξσ M hmatch
  refine ⟨Ncost,hM,?_⟩
  intro n hn hn0 D qCount hD F hF Allowed hAllowed i₀ rsv ρ₀ smin hsmin hρ hρlo hρhi sampling
    rstar k P π Cres w seed τ tMatch ξMatch bMatch ζDel ζevent χpair χlist χbal χbd χnbr χpairR χpath aEvent αOriginal BO hwitness
    r mAbs ξabs A Z Wterm Bterm B σx raw Bad Reference Href Kabs JQ JH hw cost
  have hh:=hcost n hn hn0 D qCount hD F hF Allowed hAllowed i₀ rsv ρ₀ smin hsmin hρ hρlo hρhi sampling
    rstar k P π Cres w seed τ tMatch ξMatch bMatch ζDel ζevent χpair χlist χbal χbd χnbr χpairR χpath aEvent αOriginal BO hwitness
    r mAbs ξabs A Z Wterm Bterm B σx Kabs JQ JH hw
  simpa [cost,ordinaryTriangleAssignedReservoirCost] using hh
end Oberwolfach
