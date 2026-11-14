module

public import Oberwolfach.MarkedTerminalAbsorberAmbientLift
public import Oberwolfach.MarkedPackingSpokesInHost
public import Oberwolfach.MarkedFinitePackingIteration

@[expose] public section
/-! A universal terminal absorber already decomposes its reserve and hence
uses only resources of the original marked host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]

theorem marked_universal_terminal_absorber_supported_in_host
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (Reserve:Finset (Finset V⊕(V×U))) (X:Finset V) (Z:Finset U)
    (habs:MarkedUniversalTerminalDeletionAbsorber P π d m σ H Reserve X Z):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let S:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2);
    HasResourceDecomposition
      (fun W:MarkedWheel (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
        m π (3*d) (H false) (H true)=>markedWheelPhysicalResources W) Reserve ∧
    Reserve⊆markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π Finset.univ S:=by
  intro E K S
  let DR:SimpleGraph V:=⊥
  let DS:SimpleGraph (V⊕U):=⊥
  have hEq:(fun (a b:V)=>Classical.propDecidable (a=b))=(inferInstance:DecidableEq V):=by
    apply Subsingleton.elim
  have habs':=habs
  try rw [←hEq] at habs'
  have hdec:=marked_terminal_absorber_decomposition_lift P π d m σ H Reserve X Z habs' DR DS
    (by intro x y h; simp [DR]) (by intro v u h; simp [DS]) (by intro v hv u hu; simp [DS])
    ∅ ∅ (by simp) (by simp) (by constructor <;> simp)
  try rw [hEq] at hdec
  have hdec':HasResourceDecomposition
      (fun W:MarkedWheel (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
        m π (3*d) (H false) (H true)=>markedWheelPhysicalResources W) Reserve:=by
    simpa [markedFiniteResources] using hdec
  refine ⟨hdec',?_⟩
  obtain ⟨M,hM,hres⟩:=hdec'
  rw [←hres,←markedPackingResources_eq_finite]
  exact markedFiniteResources_mono (Finset.subset_univ _) (marked_packing_spokes_subset_host M)
end Oberwolfach
