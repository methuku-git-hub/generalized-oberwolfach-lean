module

public import Oberwolfach.MarkedPhysicalDeletionComposition
public import Oberwolfach.MarkedRegularHostRobustAbsorberJointEvent

@[expose] public section

/-! A robust absorber on the parent sample remains available after two
successive physical deletions, provided their global degree budgets add up
to the robustness margin. This does not establish those budgets for a
particular cover-down. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_robust_absorber_after_two_physical_deletions
    (P:SimpleGraph V) (π:Equiv.Perm V) (d r size a₀ b₀ e₀ f₀:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop) (ε ζ cR₁ cR₂ cS₁ cS₂:ℝ)
    (hrob:∀ (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)),
      (∀ x,(DR.degree x:ℝ)≤ζ*Fintype.card V)→
      (∀ x,(DS.degree x:ℝ)≤ζ*Fintype.card V)→
      let σ':=rawMarkedDeleteRims σ DR.edgeFinset
      let H':=markedDeletePhysicalSpokes H DS
      MarkedReservedTerminalAbsorberProperty
        (fun e:MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
        (fun e:MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
        (H' false) (H' true) π (3*d) r size a₀ b₀ e₀ f₀ ε)
    (R₁ R₂:SimpleGraph V) (S₁ S₂:SimpleGraph (V⊕U))
    (hR₁:∀ x,(R₁.degree x:ℝ)≤cR₁) (hR₂:∀ x,(R₂.degree x:ℝ)≤cR₂)
    (hS₁:∀ x,(S₁.degree x:ℝ)≤cS₁) (hS₂:∀ x,(S₂.degree x:ℝ)≤cS₂)
    (hR:cR₁+cR₂≤ζ*Fintype.card V) (hS:cS₁+cS₂≤ζ*Fintype.card V):
    let σ':=rawMarkedDeleteRims (rawMarkedDeleteRims σ R₁.edgeFinset) R₂.edgeFinset
    let H':=markedDeletePhysicalSpokes (markedDeletePhysicalSpokes H S₁) S₂
    MarkedReservedTerminalAbsorberProperty
      (fun e:MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
      (fun e:MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
      (H' false) (H' true) π (3*d) r size a₀ b₀ e₀ f₀ ε:=by
  have hRsup:∀ x,((R₁⊔R₂).degree x:ℝ)≤ζ*Fintype.card V:=by
    intro x
    have hdeg:((R₁⊔R₂).degree x:ℝ)≤(R₁.degree x:ℝ)+(R₂.degree x:ℝ):=by
      exact_mod_cast graph_degree_sup_le R₁ R₂ x
    exact hdeg.trans ((add_le_add (hR₁ x) (hR₂ x)).trans hR)
  have hSsup:∀ x,((S₁⊔S₂).degree x:ℝ)≤ζ*Fintype.card V:=by
    intro x
    have hdeg:((S₁⊔S₂).degree x:ℝ)≤(S₁.degree x:ℝ)+(S₂.degree x:ℝ):=by
      exact_mod_cast graph_degree_sup_le S₁ S₂ x
    exact hdeg.trans ((add_le_add (hS₁ x) (hS₂ x)).trans hS)
  have h:=hrob (R₁⊔R₂) (S₁⊔S₂)
    (by intro x; simpa only [←SimpleGraph.ncard_neighborSet] using hRsup x)
    (by intro x; simpa only [←SimpleGraph.ncard_neighborSet] using hSsup x)
  dsimp only at h ⊢
  rw [rawMarkedDeleteRims_sup,markedDeletePhysicalSpokes_sup]
  convert h using 1 <;> congr!
end Oberwolfach
