module

public import Oberwolfach.MarkedVortexFiniteSampleChain
public import Oberwolfach.RawMarkedRetention
public import Oberwolfach.RetainedMarkedSpokeChanges

@[expose] public section
/-! Specialization of the coherent vortex chain to the exact retained sample
and its physical spoke relation. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ}

theorem marked_vortex_retained_finite_sample_chain_exists
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hπ:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d:ℕ) (a:Γ) (j:Color)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (count:ℕ) (hc:0<count):
    let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j;
    Nonempty (MarkedVortexFiniteSampleChain Q π hπ z.1 H count hc) := by
  intro H
  exact marked_vortex_finite_sample_chain_exists Q π hπ z.1 H count hc
theorem marked_vortex_retained_complete_sample_chain_exists
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hπ:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d:ℕ) (a:Γ) (j:Color)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a):
    let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j;
    Nonempty (MarkedVortexFiniteSampleChain Q π hπ z.1 H Q.length Q.length_pos) := by
  intro H
  exact marked_vortex_finite_sample_chain_exists Q π hπ z.1 H Q.length Q.length_pos
end Oberwolfach
