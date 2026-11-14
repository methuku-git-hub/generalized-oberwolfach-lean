module

public import Oberwolfach.MarkedReferenceDeletionComposeValid
public import Oberwolfach.MarkedFixedTerminalAbsorberOriginal
public import Oberwolfach.MarkedReferenceAbsorberDeletion

@[expose] public section
/-! A terminal absorber selected in the corrected sample can be added to the
initial reference deletion, with its exact physical remainder and budgets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_reference_correction_then_reserve
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop) (X:Finset V) (Y:Finset U) (γ₀ σ₀ e:ℝ)
    (D₀:MarkedReferenceDeletion P π d σ) (h₀:D₀.Valid H m X Y γ₀ σ₀)
    (hsep:∀v u,¬(H false v u∧H true v u)):
    let σ':=rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ D₀.arcs).edgeFinset
    let H':=markedDeletePhysicalSpokes H (markedFiniteSpokeGraph D₀.spokes);
    ∀ (Reserve:Finset (Finset V⊕(V×U))) (Xterm:Finset V) (Yterm:Finset U),
      MarkedFixedTerminalAbsorber P π d m σ' H' Reserve Xterm Yterm →
      Reserve.filter (markedInnerResource X Y)=∅ → (Reserve.card:ℝ)≤e →
      ∃ D₂:MarkedReferenceDeletion P π d σ,
        D₂.Valid H m X Y (γ₀+e) (σ₀+e) ∧
        D₂.removed=D₀.removed∪Reserve ∧
        D₂.remaining H=D₀.remaining H\Reserve ∧
        Disjoint D₀.removed Reserve := by
  intro σ' H' Reserve Xterm Yterm habs hempty hcard
  have hsep':∀v u,¬(H' false v u∧H' true v u):=by
    intro v u hh
    apply hsep v u
    exact ⟨hh.1.1,hh.2.1⟩
  let E:=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
  let K:=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true
  have hdec:HasResourceDecomposition
      (fun W:MarkedWheel (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
        m π (3*d) (H' false) (H' true)=>markedWheelPhysicalResources W) Reserve:=
    (marked_fixed_terminal_absorber_supported_in_host P π d m σ' H' Reserve Xterm Yterm habs).1
  have hdiv:=h₀.2.2.2.2
  obtain ⟨D₁,h₁,hremoved,hremain⟩:=marked_reference_absorber_deletion P π d m σ' H' X Y e e
    hsep' hdiv Reserve hdec hempty hcard hcard
  let D₂:=markedReferenceDeletionCompose P π d σ D₀ D₁
  have hvalid:D₂.Valid H m X Y (γ₀+e) (σ₀+e):=
    marked_reference_deletion_compose_valid P π d m σ H X Y γ₀ σ₀ e e e D₀ h₀ D₁ h₁ (by rw [hremoved];exact hcard)
  have hD₂:D₂.removed=D₀.removed∪Reserve:=by
    rw [marked_reference_deletion_compose_removed,hremoved]
  have hdis:=marked_reference_deletion_compose_disjoint P π d m σ H X Y e e D₀ D₁ h₁
  have hfull:D₀.remaining H=markedFiniteResources
      (fun a:E=>a.val.1) (fun a=>a.val.2) (fun a:K=>a.val.1) (fun a=>a.val.2) π Finset.univ
      (Finset.univ.filter (fun z:V×U=>H' false z.1 z.2∨H' true z.1 z.2)):=by
    have hh:=marked_deleted_sample_resources P π d σ H D₀.arcs D₀.spokes
    simpa only [MarkedReferenceDeletion.remaining,MarkedReferenceDeletion.removed] using hh.symm
  refine ⟨D₂,hvalid,hD₂,?_,?_⟩
  · rw [marked_reference_deletion_compose_remaining,hremain,←hfull]
  · simpa only [hremoved] using hdis.2.1
end Oberwolfach
