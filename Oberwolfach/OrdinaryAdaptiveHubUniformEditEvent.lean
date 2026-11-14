module

public import Oberwolfach.OrdinaryEditEnvelopeMarginChoices
public import Oberwolfach.OrdinaryAdaptiveHubEventEditEnvelope

@[expose] public section
/-! Event margins can be chosen independently of the later edited host;
one pre-sampled event then covers every actual edit within the envelope. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_adaptive_hub_uniform_edit_event
    (eParent hParent:ℝ) (he:0<eParent) (hh:0<hParent):
    ∃eEvent hEvent cap:ℝ,0<eEvent ∧ 0<hEvent ∧ 0<cap ∧
      eEvent ≤ eParent ∧ hEvent ≤ hParent ∧
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀(m:ℕ) (P F:SimpleGraph V) (X:Finset V) (Z:Finset U)
      (π:Equiv.Perm V) (d:ℕ) (pR pH density tR tH ε Lold Lnew b B η:ℝ)
      (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color),
    0 ≤ ε → 0 ≤ Lold → Lold ≤ Lnew →
    (X.card:ℝ) ≤ ε*Fintype.card (V⊕U) → Lnew ≤ cap*X.card →
    OrdinaryAdaptiveHubWeightsInnerScaleLevelEvent m P F X Z π d pR pH density tR tH Lnew
      (eEvent*ε) (hEvent*ε) b B η s j raw →
    OrdinaryAdaptiveHubWeightsInnerScaleLevelEvent m P F X Z π d pR pH density tR tH Lold
      (eParent*ε) (hParent*ε) b B η s j raw :=by
  obtain ⟨eEvent,hEvent,cap,heEvent,hhEvent,hcap,heBound,hhBound,hmargin⟩:=
    ordinary_edit_envelope_margin_choices eParent hParent he hh
  refine ⟨eEvent,hEvent,cap,heEvent,hhEvent,hcap,heBound,hhBound,?_⟩
  intro V U Γ Color _ _ _ _ _ _ m P F X Z π d pR pH density tR tH ε Lold Lnew b B η s j raw
    hε hLold hL hX hLnew event
  obtain ⟨hE,hH⟩:=hmargin ε (Fintype.card (V⊕U)) X.card Lold Lnew hε (by positivity) (by positivity)
    hLold hL hX hLnew
  exact ordinary_adaptive_hub_event_of_edit_envelope m P F X Z π d pR pH density tR tH Lold Lnew
    (eParent*ε) (hParent*ε) (eEvent*ε) (hEvent*ε) b B η s j raw event hL hE hH
end Oberwolfach
