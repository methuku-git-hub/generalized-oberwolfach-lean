module

public import Oberwolfach.OrdinaryInducedHubTargetsFromCleanup
public import Oberwolfach.OrdinaryMixedHubWeightsFromInducedPotentials

@[expose] public section
/-! On the same raw sample, the original-law potential event and cleanup
profile construct the mixed hub weights with fixed parent coefficients. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3000000
set_option synthInstance.maxSize 4096
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]

def ordinary_mixed_hub_weights_from_sample
    (P Q F : SimpleGraph V) (H : V → U → Prop) (A : Finset V) (Z : Finset U)
    (π : Equiv.Perm V) (d : ℕ) (hd : 2≤d) (j : Color)
    (hconf : permutationConflictGraph π (3*d)≤F)
    (hnoshort : ∀ x k,0<k → k<2*d+1 → (π^k) x≠x)
    (p pR pH D δ ξ Lconf cLo cHi b Bweight η K : ℝ)
    (hA:0<A.card) (hQP:Q≤P) (hp:0<p) (hp1:p≤1)
    (hpR:p≤pR) (hpR1:pR≤1) (hpH:p≤pH) (hpH1:pH≤1)
    (hδ:0≤δ) (hL:0≤Lconf) (hcLo:0<cLo) (hcHi:0≤cHi) (hK:0≤K)
    (hDlo:(A.card:ℝ)/2≤D) (hDhi:D≤2*A.card)
    (hreg:∀v:{v:V // v∈(A:Set V)},|((P.induce (A:Set V)).degree v:ℝ)-D|≤δ*A.card)
    (hF:∀v:{v:V // v∈(A:Set V)},((F.induce (A:Set V)).degree v:ℝ)≤Lconf)
    (weight:OrdinaryCycle (P.induce (A:Set V)) 3→ℝ)
    (hweight:∀C,cLo/(A.card:ℝ)≤weight C∧weight C≤cHi/(A.card:ℝ))
    (hedge:∀x y,(∑C,if C.val.val.Adj x y then weight C else 0)=if (P.induce (A:Set V)).Adj x y then 1 else 0)
    (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (σ:RawWheelOutcome V U Γ Color) (Bpot t Ledit density tR tH βe βh:ℝ)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d A Z pR pH density tR tH Ledit βe βh s j σ)
    (hsize:(Fintype.card V:ℝ)≤K*A.card) (hb:b≤cLo) (hB:(4*cHi/p^7)*K^2≤Bweight)
    (herr:ξ+2*δ+12*(3:ℝ)^4*cHi*Lconf/A.card≤η):
    let μ:=rawWheelLaw (fun _ : Sym2 V=>pR) (fun _=>by linarith) (fun _=>hpR1) d hd q hq hQ s hs hS;
    ordinaryInducedEditedPotentialConcentration P F (A:Set V) π d 3 j
      (fun C=>2*weight C/(D*pR^3*pH^2)) μ Bpot t Ledit Ledit σ→
    t+(3:ℝ)^2*Bpot*Ledit/Fintype.card {x:V // x∈(A:Set V)}+
      2*(3*(3:ℝ)^4*Bpot*Ledit/Fintype.card {x:V // x∈(A:Set V)})≤ξ→
    OrdinaryMixedHubWeights b Bweight η Q F H A Z:=by
  intro μ hevent hmargin
  have hpRpos:0<pR:=hp.trans_le hpR
  have hpHpos:0<pH:=hp.trans_le hpH
  have hApos:(0:ℝ)<A.card:=Nat.cast_pos.mpr hA
  have hDpos:0<D:=by linarith
  have hpot := ordinary_induced_hub_targets_from_cleanup P Q F H A Z π d hd j hconf hnoshort weight D pR pH
    hpRpos hpR1 hpHpos hDpos.ne' q hq hQ s hs hS σ Bpot t Ledit ξ density tR tH βe βh profile
    hevent hmargin
  exact ordinary_mixed_hub_weights_from_induced_potentials P Q F H A Z p pR pH D δ ξ Lconf cLo cHi b Bweight η K
    hA hQP hp hp1 hpR hpR1 hpH hpH1 hδ hL hcLo hcHi hK hDlo hDhi hreg hF weight hweight hedge hpot hsize hb hB herr
end Oberwolfach
