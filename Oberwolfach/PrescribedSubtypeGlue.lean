module

public import Oberwolfach.PrescribedEmbeddingGlue

@[expose] public section
/-! A remainder whose vertices have their own finite type can be glued to a
previously embedded part of the original factor through an embedding into
its vertex set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X Y V:Type} [Fintype X] [DecidableEq X] [DecidableEq Y] [DecidableEq V] [Nonempty V]

theorem prescribed_subtype_embeddings_glue (embed:X↪Y) (A:Finset Y) (ψ:Y→V) (Φ:X→V)
    (hψ:Set.InjOn ψ (↑A:Set Y)) (hΦ:Function.Injective Φ)
    (hAgree:∀x,embed x∈A→Φ x=ψ (embed x))
    (hAvoid:∀x,embed x∉A→Φ x∉A.image ψ):
    ∃g:Y→V,Set.InjOn g (↑(A∪Finset.univ.image embed):Set Y) ∧
      (∀y∈A,g y=ψ y) ∧ (∀x,g (embed x)=Φ x) := by
  let Q:Finset Y:=Finset.univ.image embed
  let v₀:V:=Classical.choice inferInstance
  let lift:Y→V:=fun y=>if hy:y∈Q then Φ (Classical.choose (Finset.mem_image.mp hy)) else v₀
  have hlift:∀x,lift (embed x)=Φ x:=by
    intro x
    have hx:embed x∈Q:=Finset.mem_image.mpr ⟨x,Finset.mem_univ x,rfl⟩
    dsimp [lift]
    rw [dif_pos hx]
    have hh:=Classical.choose_spec (Finset.mem_image.mp hx)
    have heq:Classical.choose (Finset.mem_image.mp hx)=x:=embed.injective hh.2
    rw [heq]
  have hliftInj:Set.InjOn lift (↑Q:Set Y):=by
    intro y hy z hz heq
    obtain ⟨x,_,rfl⟩:=Finset.mem_image.mp hy
    obtain ⟨x',_,rfl⟩:=Finset.mem_image.mp hz
    rw [hlift,hlift] at heq
    exact congrArg embed (hΦ heq)
  have hag:∀y∈A∩Q,ψ y=lift y:=by
    intro y hy
    obtain ⟨hyA,hyQ⟩:=Finset.mem_inter.mp hy
    obtain ⟨x,_,rfl⟩:=Finset.mem_image.mp hyQ
    rw [hlift]
    exact (hAgree x hyA).symm
  have hav:∀y∈Q\A,∀z∈A,lift y≠ψ z:=by
    intro y hy z hz
    obtain ⟨hyQ,hyA⟩:=Finset.mem_sdiff.mp hy
    obtain ⟨x,_,rfl⟩:=Finset.mem_image.mp hyQ
    rw [hlift]
    intro heq
    exact hAvoid x hyA (Finset.mem_image.mpr ⟨z,hz,heq.symm⟩)
  obtain ⟨g,hginj,hgA,hgQ⟩:=prescribed_embeddings_glue A Q ψ lift hψ hliftInj hag hav
  refine ⟨g,hginj,hgA,?_⟩
  intro x
  have hx:embed x∈Q:=Finset.mem_image.mpr ⟨x,Finset.mem_univ x,rfl⟩
  rw [hgQ (embed x) hx,hlift]
end Oberwolfach
