module

public import Oberwolfach.MarkedRetainedArcDegreeRelabel
public import Oberwolfach.MarkedReferenceStatisticsSampleDegrees

@[expose] public section
/-! Transport the initial vortex reference rim-degree estimates to the
original host through the canonical full-domain relabelling. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [Nonempty V] [Nonempty W]
  [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem marked_reference_relabel_sample_degrees
    (F:W↪oV) (f:W≃V) (hf:∀w,f w=F w) (uEq:Z≃U)
    (π:Equiv.Perm V) (ρ:Equiv.Perm W) (hc:∀w,f (ρ w)=π (f w))
    (P:SimpleGraph V) (d:ℕ) (a g:Γ) (j:Color)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (D ε δ γ p k s₀ t₀:ℝ)
    (hstats:MarkedReferenceStatistics (P.comap F) ρ d g j D ε δ γ p k s₀ t₀
      (markedRetainedPairRestriction f uEq π ρ hc d a z).1):
    let E:=MarkedSampleArc P π (3*d) (fun e=>z.1 (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>z.1 (Sum.inl e)) true;
    (∀v,|occurrenceDegree (fun e:E=>e.val.1) v-p*D|≤ε*Fintype.card V) ∧
    (∀v,|occurrenceDegree (fun e:E=>e.val.2) v-p*D|≤ε*Fintype.card V) ∧
    (∀v,|occurrenceDegree (fun e:K=>e.val.1) v-k*D|≤ε*Fintype.card V) ∧
    (∀v,|occurrenceDegree (fun e:K=>e.val.2) v-k*D|≤ε*Fintype.card V):=by
  intro E K
  obtain ⟨hdo,hdi,hko,hki⟩:=marked_reference_statistics_sample_arc_degrees (P.comap F) ρ d g j D ε δ γ p k s₀ t₀
    (markedRetainedPairRestriction f uEq π ρ hc d a z).1 hstats
  have hcard:Fintype.card W=Fintype.card V:=Fintype.card_congr f
  refine ⟨?_,?_,?_,?_⟩ <;> intro v
  · have hh:=hdo (f.symm v)
    rw [(marked_retained_arc_degrees_relabel F f hf uEq π ρ hc P d a z false (f.symm v)).1,hcard] at hh
    simpa only [Equiv.apply_symm_apply] using hh
  · have hh:=hdi (f.symm v)
    rw [(marked_retained_arc_degrees_relabel F f hf uEq π ρ hc P d a z false (f.symm v)).2,hcard] at hh
    simpa only [Equiv.apply_symm_apply] using hh
  · have hh:=hko (f.symm v)
    rw [(marked_retained_arc_degrees_relabel F f hf uEq π ρ hc P d a z true (f.symm v)).1,hcard] at hh
    simpa only [Equiv.apply_symm_apply] using hh
  · have hh:=hki (f.symm v)
    rw [(marked_retained_arc_degrees_relabel F f hf uEq π ρ hc P d a z true (f.symm v)).2,hcard] at hh
    simpa only [Equiv.apply_symm_apply] using hh
end Oberwolfach
