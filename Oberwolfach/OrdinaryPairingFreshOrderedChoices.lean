module

public import Oberwolfach.OrdinaryPairingOrderedHierarchy
public import Oberwolfach.OrdinaryGeneralFreshPairingProbabilityProperty

@[expose] public section
/-! Choose the endpoint scale before the pairing theorem, then choose the
    edit tolerance after its actual accuracy and any later positive cap. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_pairing_fresh_ordered_choices
    (m:ℕ) (hm:3≤m) (γ κ b B p₀ κinner K:ℝ)
    (hγ:0<γ) (hκ:0<κ) (hb:0<b) (hB:0≤B) (hp₀:0<p₀) (hp₀1:p₀≤1)
    (hκinner:0<κinner) (hK:0<K):
    ∃a εf ηf ζ:ℝ,0<a ∧ a≤1 ∧ 0<εf ∧ 0<ηf ∧ 0<ζ ∧
      OrdinaryGeneralFreshPairingProbabilityProperty m γ κ b B p₀ a εf ηf ζ ∧
    ∀cap:ℝ,0<cap→∃lam:ℝ,0<lam ∧ lam≤cap ∧
      a*K+2*lam≤p₀/2 ∧ a*K+2*lam≤p₀*κinner ∧ 6*lam≤ηf*a :=by
  obtain ⟨a,ha,ha1,hordered⟩:=ordinary_pairing_ordered_hierarchy p₀ κinner K hp₀ hκinner hK
  obtain ⟨εf,ηf,ζ,hεf,hηf,hζ,hprob⟩:=ordinary_general_fresh_pairing_probability_property m hm γ κ b B p₀ a
    hγ hκ hb hB hp₀ hp₀1 ha ha1
  refine ⟨a,εf,ηf,ζ,ha,ha1,hεf,hηf,hζ,hprob,?_⟩
  intro cap hcap
  obtain ⟨lam,hlam,hR,hH,herr⟩:=hordered ηf hηf
  let lam':=min lam cap
  have hl:0<lam':=lt_min hlam hcap
  have hl0:lam'≤lam:=min_le_left _ _
  refine ⟨lam',hl,min_le_right _ _,?_,?_,?_⟩ <;> linarith
end Oberwolfach
