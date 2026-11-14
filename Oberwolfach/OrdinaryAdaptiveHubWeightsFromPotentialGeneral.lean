module

public import Oberwolfach.OrdinaryInducedHubTargetsFromCleanupGeneral
public import Oberwolfach.OrdinaryHubWeightsOfSetupGeneral

@[expose] public section
/-! The adaptive potential event yields hub weights for every cleanup of
    the same outcome, using the fixed inner parent setup. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3000000
set_option synthInstance.maxSize 8192
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_adaptive_hub_weights_from_potential_general
    (m:ℕ) (hm:2≤m)
    (P F:SimpleGraph V) (A:Finset V) (Z:Finset U) (π:Equiv.Perm V) (d:ℕ) (hd:2≤d) (j:Color)
    (hconf:permutationConflictGraph π (3*d)≤F)
    (hnoshort:∀x k,0<k→k<2*d+1→(π^k) x≠x)
    (pmin pR pH D δ ξ Lconf cLo cHi b Bweight η K t Ledit density tR tH βe βh:ℝ)
    (weight:OrdinaryCycle (P.induce (A:Set V)) (m+1)→ℝ)
    (setup:OrdinaryInnerHubWeightSetupGeneral m P F A weight pmin pR pH D δ ξ Lconf cLo cHi b Bweight η K)
    (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (σ:RawWheelOutcome V U Γ Color) (Bpot:ℝ) :
    let hpR : 0<pR := setup.ppos.trans_le setup.rimlo;
    let raw:=rawWheelLaw (fun _ : Sym2 V=>pR) (fun _=>hpR.le) (fun _=>setup.rimhi) d hd q hq hQ s hs hS;
    ordinaryInducedEditedPotentialConcentration P F (A:Set V) π d (m+1) j
      (fun C=>2*weight C/(D*pR^(m+1)*pH^m)) raw Bpot t Ledit Ledit σ →
    t+((m+1:ℕ):ℝ)^2*Bpot*Ledit/Fintype.card (A:Set V)+
      2*(3*((m+1:ℕ):ℝ)^4*Bpot*Ledit/Fintype.card (A:Set V))≤ξ →
    ∀(Q:SimpleGraph V) (H:V→U→Prop),
      OrdinaryCleanupParentProfiles P Q F H π d A Z pR pH density tR tH Ledit βe βh s j σ →
      Q≤P → Nonempty (OrdinaryMixedHubWeightsOfLength m b Bweight η Q F H A Z) := by
  intro hpR raw hpot hmargin Q H profile hQP
  have hpH:0<pH:=setup.ppos.trans_le setup.spokelo
  have hD:0<D:=by have hh:(0:ℝ)<A.card:=Nat.cast_pos.mpr setup.Apos; linarith [setup.center_lower]
  have htarget:=ordinary_induced_hub_targets_from_cleanup_general m P Q F H A Z π d hd j hconf hnoshort weight D pR pH
    hpR setup.rimhi hpH hD.ne' q hq hQ s hs hS σ Bpot t Ledit ξ density tR tH βe βh profile hpot hmargin
  exact ⟨ordinary_hub_weights_of_setup_general m hm P Q F H A Z weight pmin pR pH D δ ξ Lconf cLo cHi b Bweight η K
    setup hQP htarget⟩
end Oberwolfach
