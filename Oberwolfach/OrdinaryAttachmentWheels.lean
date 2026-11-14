module

public import Oberwolfach.OrdinaryFiniteAttachments
public import Oberwolfach.OrdinaryWheelFamilies

@[expose] public section

/-! The extra attachment edges have a decomposition into the actual
private wheels, including when several wheels share the same old root. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I W : Type} [Fintype V] [Fintype U] [Fintype I] [Fintype W]
    [DecidableEq V] [DecidableEq U] [DecidableEq I] [DecidableEq W] {r : ℕ}

def finiteAttachmentWheel (C : SimpleGraph W) (hC : IsEmbeddedCycle C r) (z : W) (ρ : I → V) (i : I) :
    OrdinaryWheel (ordinaryAttachmentRim ⊥ C z ρ) ⊥
      (ordinaryAttachmentSpokes (fun (_ : V) (_ : U) => False) z ρ) r := by
  let D := C.map (attachmentWheelEmbedding z ρ i)
  have hD : IsEmbeddedCycle D r := hC.map _
  have hDQ : D≤ordinaryAttachmentRim ⊥ C z ρ := by
    rw [ordinaryAttachmentRim_eq]
    exact le_sup_of_le_right (le_iSup (fun j => C.map (attachmentWheelEmbedding z ρ j)) i)
  refine ⟨(⟨⟨D,hD⟩,hDQ⟩,Sum.inr i),?_,?_⟩
  · intro a ha
    change a∈(C.map (attachmentWheelEmbedding z ρ i)).support at ha
    rw [SimpleGraph.support_map] at ha
    obtain ⟨w,hw,rfl⟩ := ha
    by_cases hwz : w=z <;> simp [attachmentWheelEmbedding,ordinaryAttachmentSpokes,hwz]
  · intro a b ha hb
    exact not_false

theorem finiteAttachmentWheel_rim (C : SimpleGraph W) (hC : IsEmbeddedCycle C r) (z : W) (ρ : I → V) (i : I) :
    ordinaryWheelRim (finiteAttachmentWheel (U:=U) C hC z ρ i)=C.map (attachmentWheelEmbedding z ρ i) := rfl

theorem finiteAttachmentWheel_hub (C : SimpleGraph W) (hC : IsEmbeddedCycle C r) (z : W) (ρ : I → V) (i : I) :
    ordinaryWheelHub (finiteAttachmentWheel (U:=U) C hC z ρ i)=Sum.inr i := rfl

theorem finiteAttachmentWheels_disjoint (C : SimpleGraph W) (hC : IsEmbeddedCycle C r)
    (z : W) (ρ : I → V) (i j : I) (hij : i≠j) :
    Disjoint (ordinaryWheelResources (finiteAttachmentWheel (U:=U) C hC z ρ i))
      (ordinaryWheelResources (finiteAttachmentWheel C hC z ρ j)) := by
  apply ordinaryWheels_disjoint_at_one_root _ _ (Sum.inl (ρ i))
  · intro a hi hj
    rw [finiteAttachmentWheel_rim,SimpleGraph.support_map] at hi hj
    obtain ⟨w,hw,rfl⟩ := hi
    obtain ⟨w',hw',heq⟩ := hj
    by_cases hwz : w=z
    · simp [attachmentWheelEmbedding,hwz]
    · have he : attachmentWheelEmbedding z ρ j w'=Sum.inr (i,w) := by
        simpa [attachmentWheelEmbedding,hwz] using heq
      have hji := ((attachmentWheelEmbedding_private z ρ j i w' w).mp he).2.1
      exact (hij hji.symm).elim
  · simp only [finiteAttachmentWheel_hub,ne_eq,Sum.inr.injEq]
    exact hij

theorem attachment_cycle_support_spoke (C : SimpleGraph W) (z : W) (ρ : I → V)
    (hfull : ∀ w,w∈C.support) (i : I) (a : V ⊕ (I×W)) :
    a∈(C.map (attachmentWheelEmbedding z ρ i)).support ↔
      ordinaryAttachmentSpokes (fun (_ : V) (_ : U) => False) z ρ a (.inr i) := by
  rw [SimpleGraph.support_map]
  cases a with
  | inl a =>
    simp [Set.mem_image,attachmentWheelEmbedding_old,hfull,ordinaryAttachmentSpokes]
  | inr p =>
    rcases p with ⟨j,w⟩
    simp only [Set.mem_image,hfull,true_and,attachmentWheelEmbedding_private,ordinaryAttachmentSpokes]
    aesop

theorem finiteAttachmentWheel_family_rim (C : SimpleGraph W) (hC : IsEmbeddedCycle C r)
    (z : W) (ρ : I → V) :
    wheelFamilyRim (finiteAttachmentWheel (U:=U) C hC z ρ)=ordinaryAttachmentRim ⊥ C z ρ := by
  change (⨆ i,C.map (attachmentWheelEmbedding z ρ i))=ordinaryAttachmentRim ⊥ C z ρ
  rw [ordinaryAttachmentRim_eq]
  simp
  intro a b hab
  have hf : False := by simpa [SimpleGraph.map_adj'] using hab
  exact hf.elim

theorem finiteAttachmentWheel_family_spokes (C : SimpleGraph W) (hC : IsEmbeddedCycle C r)
    (z : W) (ρ : I → V) (hfull : ∀ w,w∈C.support) :
    wheelFamilySpokes (finiteAttachmentWheel (U:=U) C hC z ρ)=
      ordinaryAttachmentSpokes (fun (_ : V) (_ : U) => False) z ρ := by
  funext a b
  apply propext
  cases b with
  | inl b =>
    cases a <;> simp [wheelFamilySpokes,finiteAttachmentWheel_hub,ordinaryAttachmentSpokes]
  | inr i =>
    simp only [wheelFamilySpokes,finiteAttachmentWheel_hub,Sum.inr.injEq,finiteAttachmentWheel_rim,exists_eq_left]
    exact attachment_cycle_support_spoke C z ρ hfull i a

theorem ordinaryAttachment_extra_wheel_decomposition (C : SimpleGraph W) (hC : IsEmbeddedCycle C r)
    (z : W) (ρ : I → V) (hfull : ∀ w,w∈C.support) :
    HasOrdinaryWheelDecomposition (ordinaryAttachmentRim ⊥ C z ρ)
      (ordinaryAttachmentSpokes (fun (_ : V) (_ : U) => False) z ρ) r := by
  have h := wheelFamily_decomposition (finiteAttachmentWheel (U:=U) C hC z ρ)
    (finiteAttachmentWheels_disjoint C hC z ρ)
  rwa [finiteAttachmentWheel_family_rim,finiteAttachmentWheel_family_spokes C hC z ρ hfull] at h

end Oberwolfach
