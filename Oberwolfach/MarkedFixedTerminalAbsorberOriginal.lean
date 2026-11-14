module

public import Oberwolfach.MarkedPackingSpokesInHost
public import Oberwolfach.MarkedFinitePackingIteration
public import Oberwolfach.MarkedTwoStageTerminalAbsorber
public import Oberwolfach.GraphBottomEdgeFinsetAnyInstance

@[expose] public section
/-! A fixed absorber acts on every divisible terminal remainder in the
original host; it does not require the remainder to be a host after deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]

def MarkedFixedTerminalAbsorber
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (Reserve:Finset (Finset V⊕(V×U))) (X:Finset V) (Z:Finset U):Prop:=
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2
    let R:=fun W:MarkedWheel tail head ktail khead m π (3*d) (H false) (H true)=>markedWheelPhysicalResources W;
    ∀ (A:Finset (E⊕K)) (S:Finset (V×U)),
    (∀ a∈A,Sum.elim tail ktail a∈X∧Sum.elim head khead a∈X)→
    (∀ z∈S,z.1∈X∧z.2∈Z∧(H false z.1 z.2∨H true z.1 z.2))→
    MarkedRemainderDivisible tail head ktail khead (H true) A S m→
    IsResourceAbsorber R (markedFiniteResources tail head ktail khead π A S) Reserve

theorem marked_fixed_terminal_absorber_supported_in_host
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (Reserve:Finset (Finset V⊕(V×U))) (X:Finset V) (Z:Finset U)
    (habs:MarkedFixedTerminalAbsorber P π d m σ H Reserve X Z):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let S:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2);
    HasResourceDecomposition
      (fun W:MarkedWheel (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
        m π (3*d) (H false) (H true)=>markedWheelPhysicalResources W) Reserve ∧
    Reserve⊆markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π Finset.univ S:=by
  intro E K S
  have hdiv:MarkedRemainderDivisible (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) ∅ ∅ m:=by constructor <;> simp
  have hdec:=habs (∅:Finset (E⊕K)) ∅ (by simp) (by simp) hdiv
  have hdec':HasResourceDecomposition
      (fun W:MarkedWheel (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
        m π (3*d) (H false) (H true)=>markedWheelPhysicalResources W) Reserve:=by
    simpa [markedFiniteResources] using hdec.2.1
  refine ⟨hdec',?_⟩
  obtain ⟨M,hM,hres⟩:=hdec'
  rw [←hres,←markedPackingResources_eq_finite]
  exact markedFiniteResources_mono (Finset.subset_univ _) (marked_packing_spokes_subset_host M)
/-- The preselected absorber property implies the fixed-host property by
choosing the empty physical deletion graphs. -/
theorem marked_universal_terminal_absorber_is_fixed
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (Reserve:Finset (Finset V⊕(V×U))) (X:Finset V) (Z:Finset U)
    (habs:MarkedUniversalTerminalDeletionAbsorber P π d m σ H Reserve X Z):
    MarkedFixedTerminalAbsorber P π d m σ H Reserve X Z:=by
  have hh:=habs (⊥:SimpleGraph V) (⊥:SimpleGraph (V⊕U))
    (by intro x y he;simp) (by intro v u he;simp) (by intro v hv u hu;simp)
  unfold MarkedTerminalAbsorberForGraphs at hh
  dsimp only at hh
  rw [graph_bottom_edgeFinset_any_instance _,rawMarkedDeleteRims_empty,markedDeletePhysicalSpokes_bottom] at hh
  exact hh

end Oberwolfach
