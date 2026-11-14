module

public import Oberwolfach.MarkedSampledRobustAbsorberSharedChanges

@[expose] public section
/-! Named extra event for the same retained sample: every small corrected
host has the robust terminal absorber property. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]

def MarkedRetainedRobustChangeEvent
    (P:SimpleGraph V) (π:Equiv.Perm V) (d r:ℕ) (g:Γ) (j:Color)
    (ε ζ cap:ℝ) (size a₀ b₀ e₀ f:ℕ)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d g):Prop:=
  let H:Bool→V→U→Prop:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) g
    (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g)) z.2 g j;
  ∀ (new:RawMarkedOutcome V U Γ Color) (Hnew:Bool→V→U→Prop)
    (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U)),
    (∀ a,¬(rawMarkedPairRims P π d z.1 a↔rawMarkedPairRims P π d new a)→markedPairPhysical π a∈FR.edgeFinset)→
    (∀ b v u,¬(H b v u↔Hnew b v u)→FS.Adj (Sum.inl v) (Sum.inr u))→
    (∀ x,(FR.degree x:ℝ)≤cap*Fintype.card V)→
    (∀ x,(FS.degree x:ℝ)≤cap*Fintype.card V)→
    (∀ v u,¬(Hnew false v u∧Hnew true v u))→
  ∀ (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)),
    (∀ x,(DR.degree x:ℝ)≤ζ*Fintype.card V)→
    (∀ x,(DS.degree x:ℝ)≤ζ*Fintype.card V)→
  let σ':=rawMarkedDeleteRims new DR.edgeFinset
  let H':=markedDeletePhysicalSpokes Hnew DS;
  MarkedReservedTerminalAbsorberProperty
    (fun e:MarkedSampleArc P π (3*d) (fun a=>σ' (Sum.inl a)) false=>e.val.1) (fun e=>e.val.2)
    (fun e:MarkedSampleArc P π (3*d) (fun a=>σ' (Sum.inl a)) true=>e.val.1) (fun e=>e.val.2)
    (H' false) (H' true) π (3*d) r size a₀ b₀ e₀ f ε
end Oberwolfach
