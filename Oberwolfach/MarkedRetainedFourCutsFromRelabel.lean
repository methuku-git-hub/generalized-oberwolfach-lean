module

public import Oberwolfach.MarkedReferenceFourCutsRelabel
public import Oberwolfach.BipartiteNormalizedCutDeletion
public import Oberwolfach.MarkedSampleOccurrenceMatrix

@[expose] public section
/-! Retained-spoke agreement transfers the relabelled reference cuts to
the four actual matrices used by sparse marked correction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [Nonempty V] [Nonempty W]
  [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem marked_retained_four_cuts_from_reference_relabel
    (F:W↪oV) (f:W≃V) (hf:∀w,f w=F w) (g:Z≃U)
    (π:Equiv.Perm V) (ρ:Equiv.Perm W) (hc:∀w,f (ρ w)=π (f w))
    (P:SimpleGraph V) (d:ℕ) (a:Γ) (j:Color)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (α kstar tstar p k:ℝ) (hα:0<α) (hkstar:0<kstar) (htstar:0<tstar)
    (hpmin:kstar≤p) (hkmin:kstar≤k) (hZ:0<Fintype.card Z)
    (hcuts:MarkedReferenceCutFamilies (P.comap F) ρ d a j α p k tstar
      (markedRetainedPairRestriction f g π ρ hc d a z).1)
    (H:Bool→V→U→Prop) (ζold:ℝ) (hζold:0≤ζold)
    (hrow:∀mark x,(∑u,if ¬(rawMarkedPairSpokes π d z.1 a j mark x u↔H mark x u) then (1:ℝ) else 0)≤ζold*Fintype.card U)
    (hcol:∀mark u,(∑x,if ¬(rawMarkedPairSpokes π d z.1 a j mark x u↔H mark x u) then (1:ℝ) else 0)≤ζold*Fintype.card V)
    (hbudget:ζold≤14*(min (α*kstar) tstar/128)):
    let δ:=min (min α kstar) tstar/256
    let h:=min (α*kstar) tstar/128;
    (∀mark,BipartiteLargeCut
      (occurrenceMultiplicity (fun e:MarkedSampleArc P π (3*d) (fun e=>z.1 (Sum.inl e)) mark=>e.val.1)
        (fun e=>e.val.2)) δ (2*h)) ∧
    (∀mark,BipartiteLargeCut (relationMultiplicity (H mark)) δ (2*h)):=by
  intro δ h
  have hV:0<Fintype.card V:=Fintype.card_pos
  have hU:0<Fintype.card U:=by rw [←Fintype.card_congr g];exact hZ
  obtain ⟨hR,hS⟩:=marked_reference_four_cuts_relabel F f hf g π ρ hc P d a j z
    α kstar tstar p k hα hkstar htstar hpmin hkmin hZ hcuts
  constructor
  · intro mark
    rw [markedSampleArc_multiplicity]
    exact bipartiteLargeCut_coefficient_mono _ δ (16*h) (2*h) (by
      have hh:0≤h:=by dsimp [h];positivity
      linarith) (hR mark)
  · intro mark
    have hh:=bipartiteLargeCut_after_relation_changes hV hU _ _ δ (16*h) ζold hζold (hrow mark) (hcol mark) (hS mark)
    apply bipartiteLargeCut_coefficient_mono _ δ (16*h-ζold) (2*h) _ hh
    dsimp [h] at hbudget ⊢
    linarith
end Oberwolfach
