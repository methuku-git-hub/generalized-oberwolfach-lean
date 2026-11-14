module

public import Oberwolfach.PrescribedEmbeddingGlue

@[expose] public section
/-! New selected positions avoid the old image set when the prescribed
matching endpoints and new singleton labels do. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X V:Type} [DecidableEq X] [DecidableEq V]

theorem prescribed_selected_images_avoid_old (A B:Finset X) (f g Φ:X→V) (Old C Z:Finset V)
    (hAB:A⊆B) (hinj:Set.InjOn Φ (↑B:Set X)) (hext:∀x∈A,g x=f x) (hsame:∀x∈B,Φ x=g x)
    (himage:B.image g=A.image f∪C∪Z) (hOldC:Disjoint Old C) (hOldZ:Disjoint Old Z):
    ∀x∈B\A,Φ x∉Old := by
  intro x hx hOld
  have hxB:x∈B:=(Finset.mem_sdiff.mp hx).1
  have hxA:x∉A:=(Finset.mem_sdiff.mp hx).2
  have hm:g x∈B.image g:=Finset.mem_image.mpr ⟨x,hxB,rfl⟩
  rw [himage] at hm
  rcases Finset.mem_union.mp hm with hm|hz
  · rcases Finset.mem_union.mp hm with ha|hc
    · obtain ⟨y,hy,hxy⟩:=Finset.mem_image.mp ha
      have hyB:y∈B:=hAB hy
      have heq:Φ x=Φ y:=by rw [hsame x hxB,hsame y hyB,hext y hy];exact hxy.symm
      have hxy':x=y:=hinj hxB hyB heq
      exact hxA (by simpa [hxy'] using hy)
    · have hold':g x∈Old:=by simpa [hsame x hxB] using hOld
      exact (Finset.disjoint_left.mp hOldC) hold' hc
  · have hold':g x∈Old:=by simpa [hsame x hxB] using hOld
    exact (Finset.disjoint_left.mp hOldZ) hold' hz
end Oberwolfach
