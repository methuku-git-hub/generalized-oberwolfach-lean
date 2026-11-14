module

public import Oberwolfach.PrescribedEmbeddingBatchUpdate

@[expose] public section
/-! Two injective maps glue across their actual common domain when the new
images avoid the old image set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X V:Type} [DecidableEq X] [DecidableEq V]

theorem prescribed_embeddings_glue (A B:Finset X) (ψ φ:X→V)
    (hψ:Set.InjOn ψ (↑A:Set X)) (hφ:Set.InjOn φ (↑B:Set X))
    (hag:∀x∈A∩B,ψ x=φ x)
    (havoid:∀x∈B\A,∀y∈A,φ x≠ψ y):
    ∃g:X→V,Set.InjOn g (↑(A∪B):Set X) ∧ (∀x∈A,g x=ψ x) ∧ (∀x∈B,g x=φ x) := by
  let g:X→V:=fun x=>if x∈A then ψ x else φ x
  have hgA:∀x∈A,g x=ψ x:=by intro x hx;simp [g,hx]
  have hgB:∀x∈B,g x=φ x:=by
    intro x hx
    by_cases hA:x∈A
    · rw [hgA x hA,hag x (Finset.mem_inter.mpr ⟨hA,hx⟩)]
    · simp [g,hA]
  refine ⟨g,?_,hgA,hgB⟩
  intro x hx y hy heq
  rcases Finset.mem_union.mp hx with hxA|hxB <;> rcases Finset.mem_union.mp hy with hyA|hyB
  · exact hψ hxA hyA (by simpa [hgA x hxA,hgA y hyA] using heq)
  · by_cases hyA:y∈A
    · exact hψ hxA hyA (by simpa [hgA x hxA,hgA y hyA] using heq)
    · have hh:φ y≠ψ x:=havoid y (Finset.mem_sdiff.mpr ⟨hyB,hyA⟩) x hxA
      exact (hh (by simpa [hgA x hxA,hgB y hyB] using heq.symm)).elim
  · by_cases hxA:x∈A
    · exact hψ hxA hyA (by simpa [hgA x hxA,hgA y hyA] using heq)
    · have hh:φ x≠ψ y:=havoid x (Finset.mem_sdiff.mpr ⟨hxB,hxA⟩) y hyA
      exact (hh (by simpa [hgB x hxB,hgA y hyA] using heq)).elim
  · exact hφ hxB hyB (by simpa [hgB x hxB,hgB y hyB] using heq)
end Oberwolfach
