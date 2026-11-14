module

public import Oberwolfach.OrdinaryUniformActualPreparationEditCost
public import Oberwolfach.OrdinaryActualPreparationEditCostBound
public import Oberwolfach.OrdinaryAssignedUnusedDensityUpper

@[expose] public section
/-! The actual assigned sampling law and corrected reservoir provide the
numerical edit-cost input used by the initial wheel certificate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_actual_preparation_cost
    (m d tAbs aAbs bAbs K N dNeed:ℕ)
    (η capEdit α lamList ζList δ θ κ b z matchErr σ κ' ζret lam a γ ξedit:ℝ)
    (hm:7≤ m) (hd:2≤ d) (hK:0<K) (hda:1/θ≤ d)
    (hη:0<η) (hcap:capEdit≤ η)
    (hstage:OrdinaryPlacementStage m dNeed α lamList ζList capEdit δ θ κ b z matchErr σ κ')
    (hafter:OrdinaryPlacementAfterSpacing m d N α δ θ κ b z matchErr ζret)
    (hmatching:OrdinaryPlacementMatchingRateBounds K θ κ' b z δ matchErr lam a γ)
    (hξ:0≤ ξedit) (hξσ:ξedit≤ σ):
    ∃Ncost:ℕ,∀n:ℕ,Ncost≤ n→ 0<n→∀(D qCount:ℕ),0<D→
    ∀(F:Fin qCount→ SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
      (Allowed:Set ℕ),(∀w,AllowedCycleLengths (F w) Allowed)→
    ∀(i₀:Fin K) (rsv ρ₀ smin:ℝ),0≤ rsv→ rsv≤ 1/100→ 0<ρ₀→
      ρ₀≤ initialIndexDensity (Fin qCount) D→ initialIndexDensity (Fin qCount) D≤ 1→
      OrdinaryClassReserveBound F hF i₀ rsv→
    ∀(sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ ((m:ℝ)+1) ρ₀ smin d)
      (r mAbs:ℕ) (ξabs:ℝ) (Q Bad:SimpleGraph (Fin n)) (H:Fin n→ Fin qCount→ Prop)
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
      0≤ cost ∧ cost≤ 14*η*n :=by
  have hθ:0<θ:=hstage.2.2.2.2.1
  have hθ1:θ≤ 1/100:=hstage.2.2.2.2.2.1
  have hm':8≤ m+1:=by omega
  have hc:(8:ℝ)≤(m:ℝ)+1:=by exact_mod_cast hm'
  obtain ⟨Ncost,hcost⟩:=ordinary_uniform_actual_preparation_edit_cost_bound m d tAbs aAbs bAbs K N dNeed
    η capEdit α lamList ζList δ θ κ b z matchErr σ κ' ζret lam a γ ξedit
    hη hcap hstage hafter hmatching hξ hξσ
  refine ⟨Ncost,?_⟩
  intro n hn hn0 D qCount hD F hF Allowed hAllowed i₀ rsv ρ₀ smin hrs0 hrs1 hρ hρlo hρhi hClass
    sampling r mAbs ξabs Q Bad H A Z Wterm Bterm B Kabs JQ JH hw
  have hu:=ordinary_assigned_unused_density_upper hn0 hD F hF Allowed hAllowed K hK i₀ rsv θ ((m:ℝ)+1) ρ₀ smin d
    hd hrs0 hrs1 hθ hθ1 hc hda hρ hρlo hρhi hClass sampling
  have hresources:=ordinary_corrected_reservoir_resource_sum_bound r mAbs tAbs aAbs bAbs ξabs Q Bad H A Z Wterm Bterm B Kabs JQ JH hw
  exact hcost n hn sampling.u sampling.hu hu.2 _ _ (by positivity) (by positivity) hresources
end Oberwolfach
