module

public import Oberwolfach.OrdinaryInducedHubTargetsFromCleanup
public import Oberwolfach.OrdinaryInducedRawEditedCommon
public import Oberwolfach.OrdinaryTrianglePotentialCoefficientBounds
public import Oberwolfach.OrdinaryAdaptiveHubWeightsFromPotential

@[expose] public section
/-! One raw outcome supplies mixed hub weights for every later cleanup
    profile, with the inner parent weights fixed before sampling. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 6000000
set_option synthInstance.maxSize 8192
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_adaptive_hub_weights_raw_probability
    (P F:SimpleGraph V) (A:Finset V) (Z:Finset U) (π:Equiv.Perm V) (d:ℕ) (hd:2≤d) (j:Color)
    (hconf:permutationConflictGraph π (3*d)≤F)
    (hnoshort:∀x k,0<k→k<2*d+1→(π^k) x≠x)
    (pmin pR pH D δ ξ Lconf cLo cHi b Bweight η K t Ledit density tR tH βe βh:ℝ)
    (hcHi:0<cHi) (ht:0<t)
    (weight:OrdinaryCycle (P.induce (A:Set V)) 3→ℝ)
    (setup:OrdinaryInnerHubWeightSetup P F A weight pmin pR pH D δ ξ Lconf cLo cHi b Bweight η K)
    (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g)) :
    let hpR : 0<pR := setup.ppos.trans_le setup.rimlo;
    let raw:=rawWheelLaw (fun _ : Sym2 V=>pR) (fun _=>hpR.le) (fun _=>setup.rimhi) d hd q hq hQ s hs hS;
    let Bpot:=4*cHi/pmin^7;
    let err:=(Fintype.card (A:Set V):ℝ)*Fintype.card U *
      (2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*((3:ℝ)^4*Bpot/Fintype.card (A:Set V))*(2*3)*((3:ℝ)^2*Bpot))));
    t+(3:ℝ)^2*Bpot*Ledit/Fintype.card (A:Set V)+
      2*(3*(3:ℝ)^4*Bpot*Ledit/Fintype.card (A:Set V))≤ξ →
    1-err≤(FiniteLaw.pi raw).probability (fun σ=>∀(Q:SimpleGraph V) (H:V→U→Prop),
      OrdinaryCleanupParentProfiles P Q F H π d A Z pR pH density tR tH Ledit βe βh s j σ →
      Q≤P → Nonempty (OrdinaryMixedHubWeights b Bweight η Q F H A Z)) := by
  intro hpR raw Bpot err hmargin
  have hpH:0<pH:=setup.ppos.trans_le setup.spokelo
  have hcard:Fintype.card (A:Set V)=A.card:=by simp
  have hA:0<Fintype.card (A:Set V):=by rw [hcard]; exact setup.Apos
  have hpmin:0<pmin:=setup.ppos
  have hD:0<D:=by have hh:(0:ℝ)<A.card:=Nat.cast_pos.mpr setup.Apos; linarith [setup.center_lower]
  have hBpot:0<Bpot:=by dsimp [Bpot];positivity
  have hφ:∀ C:OrdinaryCycle (P.induce (A:Set V)) 3,
      0≤2*weight C/(D*pR^3*pH^2) ∧
      2*weight C/(D*pR^3*pH^2)≤Bpot/(Fintype.card (A:Set V):ℝ)^(3-1):=by
    have hh:=ordinary_triangle_potential_coefficient_bounds (P.induce (A:Set V)) pmin pR pH D cLo cHi
      hA setup.ppos setup.pone setup.rimlo setup.rimhi setup.spokelo setup.spokehi setup.lower_pos hcHi.le
      (by simpa only [hcard] using setup.center_lower) (by simpa only [hcard] using setup.center_upper)
      weight (by simpa only [hcard] using setup.coefficients)
    simpa only [Bpot] using hh
  have hpot:=ordinary_induced_raw_edited_common P F (A:Set V) π d 3 j (by omega)
    (by convert hA using 1 <;> simp only [Set.fintypeCard_eq_ncard])
    (fun C=>2*weight C/(D*pR^3*pH^2)) Bpot hBpot
    (by intro C; convert hφ C using 1 <;> simp only [Set.fintypeCard_eq_ncard]) raw t Ledit Ledit ht
  dsimp only [err] at *
  simp only [Set.fintypeCard_eq_ncard, Nat.cast_ofNat] at hpot ⊢
  apply hpot.trans
  apply finiteLaw_probability_mono
  intro σ hσ
  apply ordinary_adaptive_hub_weights_from_potential P F A Z π d hd j hconf hnoshort
    pmin pR pH D δ ξ Lconf cLo cHi b Bweight η K t Ledit density tR tH βe βh weight setup
    q hq hQ s hs hS σ Bpot
  · dsimp only [ordinaryInducedEditedPotentialConcentration]
    simp only [Set.fintypeCard_eq_ncard, Nat.cast_ofNat] at hσ ⊢
    exact hσ
  · exact hmargin
end Oberwolfach
