module

public import Oberwolfach.OrdinaryPairingParentFromCleanup
public import Oberwolfach.OrdinaryPairingMarginsFromScales

@[expose] public section
/-! The fixed parameter hierarchy and actual domain ratios discharge all
    endpoint size, row, column and codegree budgets of the pairing parent. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 10000000
set_option synthInstance.maxSize 8192
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

def ordinary_pairing_parent_from_scales
    (m b₀:ℕ) (P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (Z:Finset U)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (s:U→Color→ℝ)
    (γ κ b Bweight p₀ a ε η pR pH density tR tH L βe βh κinner K lam:ℝ)
    (σ:RawWheelOutcome V U Γ Color)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d A Z pR pH density tR tH L βe βh s j σ)
    (hA:A.Nonempty) (hp₀:0<p₀) (hκinner:0<κinner) (hη:0<η) (ha:0<a) (hlam:0<lam)
    (hRrate:a*K+2*lam≤p₀/2) (hHrate:a*K+2*lam≤p₀*κinner) (herr:6*lam≤η*a)
    (hsize:(Fintype.card (V⊕U):ℝ)≤K*A.card) (hZ:κinner*A.card≤(Z.card:ℝ))
    (hpR:p₀≤pR) (hpH:p₀≤pH) (hpH1:pH≤1)
    (htR:0≤tR) (htRsmall:tR≤lam*A.card) (htH:0≤tH) (htHsmall:tH≤lam*A.card)
    (hL:0≤L) (hLsmall:L≤lam*A.card)
    (hγscale:γ*Fintype.card V≤βe*Fintype.card (V⊕U))
    (hκscale:κ*Fintype.card V≤βe*Fintype.card (V⊕U))
    (hF:∀v,(F.degree v:ℝ)≤ε*Fintype.card V)
    (hFphys:∀w:V⊕U,(ordinaryPhysicalGraph F (fun _ _=>False)).degree w≤b₀)
    (hw:OrdinaryMixedHubWeightsOfLength m b Bweight η Q F H A Z):
    MixedFreshPairingParentInsideRoots m b₀ γ κ b Bweight p₀ a ε η
      (spanningRestriction Q A) F
      (ordinaryPhysicalGraph (spanningRestriction Q A) (fun v u=>H v u∧v∈A∧u∈Z))
      (ordinaryPhysicalGraph F (fun _ _=>False)) (Function.Embedding.inl:V↪V⊕U)
      (ordinaryBoundaryHubSet H Z A)
      (fun i=>(ordinaryBoundaryRimSet Q A i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet H A Z i).image Sum.inr) (fun _=>pH):=by
  have hA0:(0:ℝ)≤A.card:=by positivity
  have hAV:(A.card:ℝ)≤Fintype.card V:=by exact_mod_cast Finset.card_le_univ A
  have hVW:(Fintype.card V:ℝ)≤Fintype.card (V⊕U):=by
    exact_mod_cast Fintype.card_le_of_injective Sum.inl Sum.inl_injective
  have hnum:=ordinary_pairing_margins_from_scales p₀ κinner K η a lam A.card (Fintype.card (V⊕U)) Z.card
    pR pH density tR tH L hp₀ hκinner hη ha hlam hRrate hHrate herr hA0 (hAV.trans hVW) hsize hZ
    hpR hpH hpH1 profile.density_large htR htRsmall htH htHsmall hL hLsmall
  have hsz:=ordinary_endpoint_sizes_from_cleanup P Q F H A Z π d j s pR pH density tR tH L βe βh a σ
    profile hnum.1 hnum.2.1
  have hrow:∀x,(tH+2*L)+pH*(tH+L)≤η*(Z.filter (H x)).card:=by
    intro x
    exact (hnum.2.2 _ _ (hsz.1 x) (hsz.2 x)).1
  have hcol:∀x,(tR+2*L)+pH*(tR+L)≤η*(A∩Q.neighborFinset x).card:=by
    intro x
    exact (hnum.2.2 _ _ (hsz.1 x) (hsz.2 x)).2.1
  have hcodeg:∀x,(tH+3*L)+pH^2*(tH+L)≤η*(Z.filter (H x)).card:=by
    intro x
    exact (hnum.2.2 _ _ (hsz.1 x) (hsz.2 x)).2.2
  exact ordinary_pairing_parent_from_cleanup m b₀ P Q F H A Z π d j s γ κ b Bweight p₀ a ε η pR pH density
    tR tH L βe βh σ profile hA hpH hpH1 hγscale hκscale hF hFphys hnum.1 hnum.2.1 hrow hcol hcodeg hw
end Oberwolfach
