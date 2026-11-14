module

public import Oberwolfach.MarkedReferenceActiveAbsorberProperty
public import Oberwolfach.MarkedEmptyPhysicalDeletion
public import Oberwolfach.GraphBottomEdgeFinsetAnyInstance

@[expose] public section
/-! The absorber part of the common sampled event applies on the original
retained host by taking the empty physical deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]

theorem marked_vortex_sampled_event_original_absorber
    (r h d:ℕ) (α βconfig εref δref tol ζActive ζAbs tstar εAbs:ℝ)
    (hζ:0≤ζAbs)
    (size a₀ b₀ e₀ f₀:ℕ) (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hpres:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (L:ℕ) (s₀ p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (hevent:MarkedReferenceActiveAbsorberProperty r h d α βconfig εref δref tol ζActive ζAbs tstar εAbs
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p k q s a j z):
    let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j
    let E:=MarkedSampleArc G π (3*d) (fun e=>z.1 (Sum.inl e)) false
    let K:=MarkedSampleArc G π (3*d) (fun e=>z.1 (Sum.inl e)) true;
    MarkedReservedTerminalAbsorberProperty (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H false) (H true) π (3*d) r size a₀ b₀ e₀ f₀ εAbs :=by
  intro H E K
  have hn:0≤ζAbs*(Fintype.card V:ℝ):=mul_nonneg hζ (Nat.cast_nonneg _)
  have hr:=hevent.2 (⊥:SimpleGraph V) (⊥:SimpleGraph (V⊕U)) (by intro x;simpa using hn) (by intro x;simpa using hn)
  let adjInst:DecidableRel (⊥:SimpleGraph V).Adj:=fun a b=>Classical.propDecidable ((⊥:SimpleGraph V).Adj a b)
  let edgeInst:Fintype (⊥:SimpleGraph V).edgeSet:=@SimpleGraph.fintypeEdgeSet V ⊥ (Sym2.instFintype) adjInst
  change MarkedReservedTerminalAbsorberProperty
    (fun e:MarkedSampleArc G π (3*d) (fun e=>rawMarkedDeleteRims z.1 (@SimpleGraph.edgeFinset V ⊥ edgeInst) (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
    (fun e:MarkedSampleArc G π (3*d) (fun e=>rawMarkedDeleteRims z.1 (@SimpleGraph.edgeFinset V ⊥ edgeInst) (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
    (markedDeletePhysicalSpokes H ⊥ false) (markedDeletePhysicalSpokes H ⊥ true) π (3*d) r size a₀ b₀ e₀ f₀ εAbs at hr
  rw [graph_bottom_edgeFinset_any_instance edgeInst,rawMarkedDeleteRims_empty,markedDeletePhysicalSpokes_bottom] at hr
  exact hr
end Oberwolfach
