module

public import Oberwolfach.MarkedRetainedRobustChangeEvent
public import Oberwolfach.GraphBottomEdgeFinsetAnyInstance

@[expose] public section
/-! The shared-change event supplies the reserved absorber property on the
actual corrected sample, before its terminal remainder is chosen. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]

theorem marked_robust_changed_sample_reserved
    (P:SimpleGraph V) (π:Equiv.Perm V) (d r:ℕ) (g:Γ) (j:Color)
    (ε ζ cap:ℝ) (size a₀ b₀ e₀ f:ℕ) (hζ:0≤ζ)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d g)
    (hstable:MarkedRetainedRobustChangeEvent P π d r g j ε ζ cap size a₀ b₀ e₀ f z)
    (σ:RawMarkedOutcome V U Γ Color) (Hnew:Bool→V→U→Prop)
    (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U))
    (hR:∀a,¬(rawMarkedPairRims P π d z.1 a↔rawMarkedPairRims P π d σ a)→markedPairPhysical π a∈FR.edgeFinset)
    (hS:∀b v u,¬(retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) g
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g)) z.2 g j b v u↔Hnew b v u)→FS.Adj (Sum.inl v) (Sum.inr u))
    (hFR:∀x,(FR.degree x:ℝ)≤cap*Fintype.card V) (hFS:∀x,(FS.degree x:ℝ)≤cap*Fintype.card V)
    (htypes:∀v u,¬(Hnew false v u∧Hnew true v u)):
    MarkedReservedTerminalAbsorberProperty
      (fun e:MarkedSampleArc P π (3*d) (fun a=>σ (Sum.inl a)) false=>e.val.1) (fun e=>e.val.2)
      (fun e:MarkedSampleArc P π (3*d) (fun a=>σ (Sum.inl a)) true=>e.val.1) (fun e=>e.val.2)
      (Hnew false) (Hnew true) π (3*d) r size a₀ b₀ e₀ f ε:=by
  have hn:0≤ζ*Fintype.card V:=mul_nonneg hζ (Nat.cast_nonneg _)
  have hh:=hstable σ Hnew FR FS hR hS hFR hFS htypes (⊥:SimpleGraph V) (⊥:SimpleGraph (V⊕U))
    (by intro x;simpa using hn) (by intro x;simpa using hn)
  dsimp only at hh
  rw [graph_bottom_edgeFinset_any_instance _,rawMarkedDeleteRims_empty,markedDeletePhysicalSpokes_bottom] at hh
  exact hh
end Oberwolfach
