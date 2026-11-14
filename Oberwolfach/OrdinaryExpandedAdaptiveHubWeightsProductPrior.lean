module

public import Oberwolfach.OrdinaryAdaptiveHubWeightsRawProbability
public import Oberwolfach.OrdinaryExpandedRawEventProductPrior

@[expose] public section
/-! Adaptive inner hub weights can be added after a prior depending on the
    full expanded state and the very same physical direction coins. -/
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

theorem ordinary_expanded_adaptive_hub_weights_with_product_prior
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1) (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g))
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ρ:∀σ,FiniteLaw (R σ)) (ν:FiniteLaw (Sym2 V→Bool))
    (E:(Σσ,R σ)×(Sym2 V→Bool)→Prop) (a:ℝ)
    (P F:SimpleGraph V) (A:Finset V) (Z:Finset U) (π:Equiv.Perm V) (j:Color)
    (hconf:permutationConflictGraph π (3*d)≤F)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (pmin pH D δ ξ Lconf cLo cHi b Bweight η K t Ledit density tR tH βe βh:ℝ)
    (hcHi:0<cHi) (ht:0<t) (weight:OrdinaryCycle (P.induce (A:Set V)) 3→ℝ)
    (setup:OrdinaryInnerHubWeightSetup P F A weight pmin (2*p) pH D δ ξ Lconf cLo cHi b Bweight η K) :
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    let Bpot:=4*cHi/pmin^7;
    let err:=(Fintype.card (A:Set V):ℝ)*Fintype.card U *
      (2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*((3:ℝ)^4*Bpot/Fintype.card (A:Set V))*(2*3)*((3:ℝ)^2*Bpot))));
    t+(3:ℝ)^2*Bpot*Ledit/Fintype.card (A:Set V)+
      2*(3*(3:ℝ)^4*Bpot*Ledit/Fintype.card (A:Set V))≤ξ →
    1-a≤((μ.sigma ρ).prod ν).probability E →
    1-a-err≤((μ.sigma ρ).prod ν).probability (fun z=>E z ∧
      let raw:=fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e);
      ∀(Q:SimpleGraph V) (H:V→U→Prop),
        OrdinaryCleanupParentProfiles P Q F H π d A Z (2*p) pH density tR tH Ledit βe βh s j raw →
        Q≤P → Nonempty (OrdinaryMixedHubWeights b Bweight η Q F H A Z)) := by
  intro μ Bpot err hmargin hE
  let J:RawWheelOutcome V U Γ Color→Prop:=fun σ=>∀(Q:SimpleGraph V) (H:V→U→Prop),
    OrdinaryCleanupParentProfiles P Q F H π d A Z (2*p) pH density tR tH Ledit βe βh s j σ →
    Q≤P → Nonempty (OrdinaryMixedHubWeights b Bweight η Q F H A Z)
  let μraw:=FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>2*p) (fun _=>by linarith) (fun _=>by linarith) d hd q hq hQ s hs hS)
  have hraw := ordinary_adaptive_hub_weights_raw_probability P F A Z π d hd j hconf hnoshort
    pmin (2*p) pH D δ ξ Lconf cLo cHi b Bweight η K t Ledit density tR tH βe βh hcHi ht weight setup q hq hQ s hs hS hmargin
  have hJ:1-err≤μraw.probability J:=by
    convert hraw using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  exact ordinary_expanded_add_raw_event_with_product_prior p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS
    ρ ν E J a err hE hJ
end Oberwolfach
