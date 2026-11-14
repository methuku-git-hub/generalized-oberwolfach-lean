module

public import Oberwolfach.OrdinaryPairingParentFromScales
public import Oberwolfach.PhysicalHostDegreeBounds

@[expose] public section
/-! Construct the actual mixed pairing parent from a cleanup profile,
    its hub weights and explicit size and edit scales. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
set_option synthInstance.maxSize 16384
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_pairing_parent_from_profile
    (m b₀:ℕ) (P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (Z:Finset U)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (s:U→Color→ℝ)
    (γ κ b Bweight p₀ a εf ηf pR pH density tR tH L βe βh κinner K lam:ℝ)
    (raw:RawWheelOutcome V U Γ Color)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d A Z pR pH density tR tH L βe βh s j raw)
    (hA:A.Nonempty) (hp₀:0<p₀) (hκinner:0<κinner) (hη:0<ηf) (ha:0<a) (hlam:0<lam)
    (hRrate:a*K+2*lam≤p₀/2) (hHrate:a*K+2*lam≤p₀*κinner) (herr:6*lam≤ηf*a)
    (hsize:(Fintype.card (V⊕U):ℝ)≤K*A.card) (hZ:κinner*A.card≤(Z.card:ℝ))
    (hpR:p₀≤pR) (hpH:p₀≤pH) (hpH1:pH≤1)
    (htR:0≤tR) (htRsmall:tR≤lam*A.card) (htH:0≤tH) (htHsmall:tH≤lam*A.card)
    (hL:0≤L) (hLsmall:L≤lam*A.card)
    (hγ:0≤γ) (hκ:0≤κ) (hγβ:γ≤βe) (hκβ:κ≤βe)
    (hF:∀v,F.degree v≤b₀) (hFsmall:(b₀:ℝ)≤εf*Fintype.card V)
    (hw:Nonempty (OrdinaryMixedHubWeightsOfLength m b Bweight ηf Q F H A Z)):
    Nonempty (MixedFreshPairingParentInsideRoots m b₀ γ κ b Bweight p₀ a εf ηf
      (spanningRestriction Q A) F
      (ordinaryPhysicalGraph (spanningRestriction Q A) (fun v u=>H v u∧v∈A∧u∈Z))
      (ordinaryPhysicalGraph F (fun _ _=>False)) (Function.Embedding.inl:V↪V⊕U)
      (ordinaryBoundaryHubSet H Z A) (fun i=>(ordinaryBoundaryRimSet Q A i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet H A Z i).image Sum.inr) (fun _=>pH)) :=by
  have hcard:(Fintype.card V:ℝ)≤Fintype.card (V⊕U):=by
    exact_mod_cast Fintype.card_le_of_injective (Sum.inl:V→V⊕U) Sum.inl_injective
  have hβ:0≤βe:=hγ.trans hγβ
  have hγscale:γ*Fintype.card V≤βe*Fintype.card (V⊕U):=by
    have h1:=mul_le_mul_of_nonneg_right hγβ (Nat.cast_nonneg (Fintype.card V))
    have h2:=mul_le_mul_of_nonneg_left hcard hβ
    linarith only [h1,h2]
  have hκscale:κ*Fintype.card V≤βe*Fintype.card (V⊕U):=by
    have h1:=mul_le_mul_of_nonneg_right hκβ (Nat.cast_nonneg (Fintype.card V))
    have h2:=mul_le_mul_of_nonneg_left hcard hβ
    linarith only [h1,h2]
  have hFreal:∀v,(F.degree v:ℝ)≤εf*Fintype.card V:=by
    intro v
    have hh:(F.degree v:ℝ)≤b₀:=by exact_mod_cast hF v
    exact hh.trans hFsmall
  have hFphys:∀w:V⊕U,(ordinaryPhysicalGraph F (fun _ _=>False)).degree w≤b₀:=by
    intro w
    cases w with
    | inl v=>simpa [ordinary_physical_degree_row] using hF v
    | inr u=>simp [ordinary_physical_degree_column]
  obtain ⟨w⟩:=hw
  exact ⟨ordinary_pairing_parent_from_scales m b₀ P Q F H A Z π d j s γ κ b Bweight p₀ a εf ηf pR pH density
    tR tH L βe βh κinner K lam raw profile hA hp₀ hκinner hη ha hlam hRrate hHrate herr hsize hZ hpR hpH hpH1
    htR htRsmall htH htHsmall hL hLsmall hγscale hκscale hFreal hFphys w⟩
end Oberwolfach
