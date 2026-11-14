module

public import Oberwolfach.OrdinaryEndpointSizesFromCleanup

@[expose] public section
/-! The cleanup profile controls endpoint sizes relative to any fixed
physical inner domain whose size appears in the explicit mean budgets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_local_endpoint_sizes_from_cleanup
    (P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U) (T:Finset (V⊕U))
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (s:U→Color→ℝ)
    (pR pH density tR tH L βe βh a:ℝ) (σ:RawWheelOutcome V U Γ Color)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d A B pR pH density tR tH L βe βh s j σ)
    (hA:A.Nonempty)
    (hRbudget:a*T.card+tR+L≤pR*density*A.card)
    (hHbudget:a*T.card+tH+L≤pH*B.card):
    (∀x,a*T.card≤((A∩Q.neighborFinset x).card:ℝ)) ∧
    (∀x,a*T.card≤((B.filter (H x)).card:ℝ)):=by
  have hn:0<Fintype.card (V⊕U):=Fintype.card_pos_iff.mpr ⟨Sum.inl hA.choose⟩
  have hnR:0<(Fintype.card (V⊕U):ℝ):=by exact_mod_cast hn
  let c:ℝ:=a*T.card/Fintype.card (V⊕U)
  have hc:c*Fintype.card (V⊕U)=a*T.card:=by
    dsimp [c]
    exact div_mul_cancel₀ _ hnR.ne'
  have hr:c*Fintype.card (V⊕U)+tR+L≤pR*density*A.card:=by rw [hc];exact hRbudget
  have hh:c*Fintype.card (V⊕U)+tH+L≤pH*B.card:=by rw [hc];exact hHbudget
  have h:=ordinary_endpoint_sizes_from_cleanup P Q F H A B π d j s pR pH density tR tH L βe βh c σ profile hr hh
  simpa only [hc] using h
end Oberwolfach
