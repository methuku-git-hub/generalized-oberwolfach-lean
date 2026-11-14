module

public import Oberwolfach.MarkedReferenceAbsorberDeletion
public import Oberwolfach.MarkedDecompositionHostTransfer
public import Oberwolfach.MarkedOldInnerAgreement

@[expose] public section

/-! A reservoir chosen in one typed host can be reserved in a later host
with additions as well as deletions. Only its actual typed resources need
be preserved. Its wheel decomposition is transferred before deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_reserved_absorber_deletion_in_changed_host
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop) (X:Finset V) (Y:Finset U) (γ σloss:ℝ)
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop)
    (C:MarkedSupportedEdgeSet tail head ktail khead π U)
    (hX:∀ v,π v∈X↔v∈X)
    (hCold:∀ e∈C.edges,¬MarkedOldResource tail head ktail khead π X Y e)
    (hCdec:HasResourceDecomposition
      (fun W:MarkedWheel tail head ktail khead m π (3*d) H₀ HK=>markedWheelPhysicalResources W) C.edges)
    (hE:∀ e:E,Sum.inl ({tail e,head e}:Finset V)∈C.edges→
      ∃ e':MarkedSampleArc P π (3*d) (fun a=>σ (Sum.inl a)) false,
        e'.val.1=tail e∧e'.val.2=head e)
    (hK:∀ e:K,Sum.inl ({ktail e,π (khead e)}:Finset V)∈C.edges→
      ∃ e':MarkedSampleArc P π (3*d) (fun a=>σ (Sum.inl a)) true,
        e'.val.1=ktail e∧e'.val.2=khead e)
    (h₀:∀ v u,Sum.inr (v,u)∈C.edges→H₀ v u→H false v u)
    (hk:∀ v u,Sum.inr (v,u)∈C.edges→HK v u→H true v u)
    (hH:∀ v u,¬(H false v u∧H true v u))
    (hdiv:MarkedRemainderDivisible
      (fun e:MarkedSampleArc P π (3*d) (fun a=>σ (Sum.inl a)) false=>e.val.1) (fun e=>e.val.2)
      (fun e:MarkedSampleArc P π (3*d) (fun a=>σ (Sum.inl a)) true=>e.val.1) (fun e=>e.val.2)
      (H true) Finset.univ (Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2)) m)
    (hγ:(C.edges.card:ℝ)≤γ) (hσ:(C.edges.card:ℝ)≤σloss):
    let E':=MarkedSampleArc P π (3*d) (fun a=>σ (Sum.inl a)) false
    let K':=MarkedSampleArc P π (3*d) (fun a=>σ (Sum.inl a)) true
    let S:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2)
    let Full:=markedFiniteResources (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) π Finset.univ S;
    ∃ D:MarkedReferenceDeletion P π d σ,D.Valid H m X Y γ σloss ∧
      D.removed=C.edges ∧ D.remaining H=Full\C.edges := by
  have hdec':HasResourceDecomposition
      (fun W:MarkedWheel
        (fun e:MarkedSampleArc P π (3*d) (fun a=>σ (Sum.inl a)) false=>e.val.1) (fun e=>e.val.2)
        (fun e:MarkedSampleArc P π (3*d) (fun a=>σ (Sum.inl a)) true=>e.val.1) (fun e=>e.val.2)
        m π (3*d) (H false) (H true)=>markedWheelPhysicalResources W) C.edges :=
    marked_decomposition_transfer_on_resources C.edges hE hK h₀ hk hCdec
  have hinner:=marked_reserved_absorber_avoids_inner C X Y hX hCold
  exact marked_reference_absorber_deletion P π d m σ H X Y γ σloss hH hdiv C.edges hdec' hinner hγ hσ
end Oberwolfach
