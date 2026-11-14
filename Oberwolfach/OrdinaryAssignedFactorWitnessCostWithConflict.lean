module

public import Oberwolfach.OrdinaryAssignedPreparationCostWithConflict
public import Oberwolfach.OrdinaryOriginalSelectorFactorWitness

@[expose] public section
/-! The original factor witness supplies the class reserve and probability
bounds used by the same-sample matching and conflict estimate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_factor_witness_cost_with_conflict
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
    ∀(r mAbs:ℕ) (ξabs:ℝ) (Q Bad:SimpleGraph (Fin n)) (H:Fin n→ Fin qCount→ Prop)
      (A Z Wterm:Finset (Fin n)) (Bterm B:Finset (Fin qCount))
      (Kabs:Finset (Sym2 (Fin n)⊕(Fin n×Fin qCount))) (JQ:SimpleGraph (Fin n)) (JH:Fin n→ Fin qCount→ Prop),
    OrdinaryCorrectedProtectedReservoirWitness r mAbs tAbs aAbs bAbs ξabs Q Bad H A Z Wterm Bterm B Kabs JQ JH→
      let LF:ℝ:=2*((3*d:ℕ):ℝ);
      let edit:=ξedit*n;let t:ℝ:=(n:ℝ)^(3/5:ℝ);
      let newLoss:=5*Real.sqrt δ*n;
      let κref:ℝ:=(max a γ)*n+sampling.u*n+3*t+((6*d+4:ℕ):ℝ)+edit+LF;
      let e:ℝ:=σ*n+2*(σ*n)+LF;
      let Lrim:=edit+κref+newLoss;
      let Lspoke:=max (2*newLoss+(Lrim+e)/2) (2*(δ*n)+σ*n);
      let cost:=Lrim+Lspoke+(ordinaryResourceRows Kabs).card+(ordinaryResourceHubs Kabs).card;
      0≤ cost ∧ cost≤ 14*η*n ∧ cost+2*((3*d:ℕ):ℝ)≤15*η*n :=by
  obtain ⟨Ncost,hM,hcost⟩:=ordinary_assigned_preparation_cost_with_conflict m d tAbs aAbs bAbs K N dNeed
    η capEdit α lamList ζList δ θ κ b z matchErr σ κ' ζret lam a γ ξedit
    hm hd hK hda hη hcap hstage hafter hmatching hξ hξσ M hmatch
  refine ⟨Ncost,hM,?_⟩
  intro n hn hn0 D qCount hD F hF Allowed hAllowed i₀ rsv ρ₀ smin hsmin hρ hρlo hρhi sampling
    rstar k P π Cres w seed τ tMatch ξMatch bMatch ζDel ζevent χpair χlist χbal χbd χnbr χpairR χpath aEvent αOriginal BO hwitness
    r mAbs ξabs Q Bad H A Z Wterm Bterm B Kabs JQ JH hw
  have hrs0:0≤rsv:=(hsmin.trans_le hwitness.2.1).le
  have hrs1:rsv≤1/100:=hwitness.2.2.1
  have hClass:OrdinaryClassReserveBound F hF i₀ rsv:=hwitness.2.2.2.2.2.2.1
  exact hcost n hn hn0 D qCount hD F hF Allowed hAllowed i₀ rsv ρ₀ smin hrs0 hrs1 hρ hρlo hρhi hClass
    sampling r mAbs ξabs Q Bad H A Z Wterm Bterm B Kabs JQ JH hw
end Oberwolfach
