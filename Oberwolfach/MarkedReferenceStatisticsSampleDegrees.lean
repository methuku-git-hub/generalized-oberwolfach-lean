module

public import Oberwolfach.MarkedReferenceStatistics
public import Oberwolfach.MarkedSampleOccurrenceMatrix

@[expose] public section
/-! Reference rim statistics are exactly the four sampled-arc degree
estimates required by the global marked correction. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_reference_statistics_sample_arc_degrees
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (g:Γ) (j:Color)
    (D ε δ γ p k s₀ t₀:ℝ) (σ:RawMarkedOutcome V U Γ Color)
    (hstats:MarkedReferenceStatistics P π d g j D ε δ γ p k s₀ t₀ σ):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true;
    (∀v,|occurrenceDegree (fun e:E=>e.val.1) v-p*D|≤ε*Fintype.card V) ∧
    (∀v,|occurrenceDegree (fun e:E=>e.val.2) v-p*D|≤ε*Fintype.card V) ∧
    (∀v,|occurrenceDegree (fun e:K=>e.val.1) v-k*D|≤ε*Fintype.card V) ∧
    (∀v,|occurrenceDegree (fun e:K=>e.val.2) v-k*D|≤ε*Fintype.card V):=by
  intro E K
  refine ⟨?_,?_,?_,?_⟩ <;> intro v
  · rw [(markedSampleArc_degrees P π (3*d) (fun e=>σ (Sum.inl e)) false v).1]
    simpa only [Bool.false_eq_true,ite_false] using (hstats.1.1 false v).1
  · rw [(markedSampleArc_degrees P π (3*d) (fun e=>σ (Sum.inl e)) false v).2]
    simpa only [Bool.false_eq_true,ite_false] using (hstats.1.1 false v).2
  · rw [(markedSampleArc_degrees P π (3*d) (fun e=>σ (Sum.inl e)) true v).1]
    simpa only [ite_true] using (hstats.1.1 true v).1
  · rw [(markedSampleArc_degrees P π (3*d) (fun e=>σ (Sum.inl e)) true v).2]
    simpa only [ite_true] using (hstats.1.1 true v).2
end Oberwolfach
