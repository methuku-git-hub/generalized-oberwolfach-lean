module

public import Oberwolfach.MarkedCorrectionThenReserve
public import Oberwolfach.MarkedSelectFixedTerminalAbsorber

@[expose] public section
/-! Select a terminal reservoir in the corrected sample and compose its
removal with the original correction, preserving both budgets and resources. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_correction_select_reserve
    (P:SimpleGraph V) (π:Equiv.Perm V) (d r size a₀ b₀ e₀ f:ℕ) (ε:ℝ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (I:Finset V) (J:Finset U) (γ₀ σ₀ e:ℝ)
    (D₀:MarkedReferenceDeletion P π d σ) (h₀:D₀.Valid H (r+4) I J γ₀ σ₀)
    (hsep:∀v u,¬(H false v u∧H true v u)):
    let σ':=rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ D₀.arcs).edgeFinset
    let H':=markedDeletePhysicalSpokes H (markedFiniteSpokeGraph D₀.spokes)
    let E':=MarkedSampleArc P π (3*d) (fun x=>σ' (Sum.inl x)) false
    let K':=MarkedSampleArc P π (3*d) (fun x=>σ' (Sum.inl x)) true;
    MarkedReservedTerminalAbsorberProperty (fun x:E'=>x.val.1) (fun x=>x.val.2)
      (fun x:K'=>x.val.1) (fun x=>x.val.2) (H' false) (H' true) π (3*d) r size a₀ b₀ e₀ f ε →
    ∀ (X W:Finset V) (Z B:Finset U),
      X.card+Z.card≤size → X⊆W → Z⊆B → I⊆W → J⊆B → (∀v,π v∈I↔v∈I) →
      (W.card:ℝ)≤ε*Fintype.card V+f → (B.card:ℝ)≤ε*Fintype.card V+f →
    ∀ F₀:Finset (Finset V⊕(V×U)), F₀.card≤f → (e₀:ℝ)≤e →
    ∃ C:MarkedSupportedEdgeSet (fun x:E'=>x.val.1) (fun x=>x.val.2)
        (fun x:K'=>x.val.1) (fun x=>x.val.2) π U,
      Disjoint C.edges F₀ ∧ C.edges.card≤e₀ ∧ C.rows.card≤a₀ ∧ C.hubs.card≤b₀ ∧
      MarkedFixedTerminalAbsorber P π d (r+4) σ' H' C.edges X Z ∧
    ∃ D₂:MarkedReferenceDeletion P π d σ,
      D₂.Valid H (r+4) I J (γ₀+e) (σ₀+e) ∧
      D₂.removed=D₀.removed∪C.edges ∧ D₂.remaining H=D₀.remaining H\C.edges ∧
      Disjoint D₀.removed C.edges := by
  intro σ' H' E' K' hprop X W Z B hsize hX hZ hI hJ hπ hW hB F₀ hF he
  obtain ⟨C,hF₀,hCe,hCr,hCu,havoid,hfixed⟩:=
    marked_select_fixed_terminal_absorber P π d r size a₀ b₀ e₀ f ε σ' H' hprop
      X W I Z B J hsize hX hZ hI hJ hπ hW hB F₀ hF
  have hcard:(C.edges.card:ℝ)≤e:=by exact (Nat.cast_le.mpr hCe).trans he
  obtain ⟨D₂,h₂,hremoved,hremain,hdis⟩:=marked_reference_correction_then_reserve P π d (r+4) σ H I J γ₀ σ₀ e
    D₀ h₀ hsep C.edges X Z hfixed havoid hcard
  exact ⟨C,hF₀,hCe,hCr,hCu,hfixed,D₂,h₂,hremoved,hremain,hdis⟩
end Oberwolfach
