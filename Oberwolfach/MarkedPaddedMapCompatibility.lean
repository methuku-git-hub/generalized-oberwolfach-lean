module

public import Oberwolfach.MarkedPaddedGraphOccurrences

@[expose] public section

/-! The extended maps preserve every actual augmented rim and spoke
occurrence, in its original direction and type. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U A S I:Type} [Fintype A] [Fintype S] [Fintype I] [DecidableEq V] [DecidableEq U] [DecidableEq I]

theorem padded_maps_compatible (src dst:A→V) (row:S→V) (u:S→U) (φ φ':V→V) (ψ ψ':U→U)
    (m:ℕ) (C C':I→Fin (m+1)→V) (h h':I→U) (Z:Finset V) (B:Finset U)
    (hR:∀ a,src a∈Z∧dst a∈Z) (hS:∀ s,row s∈Z) (hU:∀ s,u s∈B)
    (hφ:∀ v∈Z,φ' v=φ v) (hψ:∀ z∈B,ψ' z=ψ z)
    (hC:∀ i k,φ' (C i k)=C' i k) (hh:∀ i,ψ' (h i)=h' i):
    (∀ e,φ' (paddingRimTail src C e)=paddingRimTail (fun a=>φ (src a)) C' e)∧
    (∀ e,φ' (paddingRimHead dst C e)=paddingRimHead (fun a=>φ (dst a)) C' e)∧
    (∀ s,φ' (paddingSpokeRow row C s)=paddingSpokeRow (fun s=>φ (row s)) C' s)∧
    (∀ s,ψ' (actualPaddingSpokeHub (m:=m) u h s)=actualPaddingSpokeHub (m:=m) (fun s=>ψ (u s)) h' s):=by
  refine ⟨?_,?_,?_,?_⟩
  · rintro (a|⟨i,k⟩)
    · exact hφ (src a) (hR a).1
    · exact hC i k
  · rintro (a|⟨i,k⟩)
    · exact hφ (dst a) (hR a).2
    · exact hC i (finRotate (m+1) k)
  · rintro (s|⟨i,k⟩)
    · exact hφ (row s) (hS s)
    · exact hC i k
  · rintro (s|⟨i,k⟩)
    · exact hψ (u s) (hU s)
    · exact hh i

theorem padded_image_resources (π:Equiv.Perm V) (src dst:A→V) (row:S→V) (u:S→U) (jr:A→Bool)
    (φ φ':V→V) (ψ ψ':U→U) (m:ℕ) (C C':I→Fin (m+1)→V) (h h':I→U) (Z:Finset V) (B:Finset U)
    (hR:∀ a,src a∈Z∧dst a∈Z) (hS:∀ s,row s∈Z) (hU:∀ s,u s∈B)
    (hφ:∀ v∈Z,φ' v=φ v) (hψ:∀ z∈B,ψ' z=ψ z)
    (hC:∀ i k,φ' (C i k)=C' i k) (hh:∀ i,ψ' (h i)=h' i):
    markedRootGraphResources π (fun e=>φ' (paddingRimTail src C e))
      (fun e=>φ' (paddingRimHead dst C e)) (fun s=>φ' (paddingSpokeRow row C s))
      (paddingRimType jr m) (fun s=>ψ' (actualPaddingSpokeHub (m:=m) u h s))=
    markedRootGraphResources π (paddingRimTail (fun a=>φ (src a)) C')
      (paddingRimHead (fun a=>φ (dst a)) C') (paddingSpokeRow (fun s=>φ (row s)) C')
      (paddingRimType jr m) (actualPaddingSpokeHub (m:=m) (fun s=>ψ (u s)) h'):=by
  obtain ⟨h₁,h₂,h₃,h₄⟩:=padded_maps_compatible src dst row u φ φ' ψ ψ' m C C' h h' Z B hR hS hU hφ hψ hC hh
  simp only [h₁,h₂,h₃,h₄]

end Oberwolfach
