module

public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section
/-! Glue a reserved-path map to a compatible embedding of its complement.
Only neighbours of the strict interior need to lie in the reserved domain. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem partial_embeddings_glue_across_interior
    {X Y:Type*} [DecidableEq X] (G:SimpleGraph X) (H:SimpleGraph Y)
    (A D:Finset X) (hDA:D⊆A)
    (fA:{x // x∈A}↪Y) (fC:{x // x∉D}↪Y)
    (hA:∀x y (hx:x∈A) (hy:y∈A),G.Adj x y→H.Adj (fA ⟨x,hx⟩) (fA ⟨y,hy⟩))
    (hC:∀x y (hx:x∉D) (hy:y∉D),G.Adj x y→H.Adj (fC ⟨x,hx⟩) (fC ⟨y,hy⟩))
    (hbound:∀x (hx:x∈A) (hxD:x∉D),fA ⟨x,hx⟩=fC ⟨x,hxD⟩)
    (hdis:∀x (hx:x∈D) y (hy:y∉D),fA ⟨x,hDA hx⟩≠fC ⟨y,hy⟩)
    (hneigh:∀x,x∈D→∀y,G.Adj x y→y∈A) :
    ∃f:X↪Y,(∀x (hx:x∈D),f x=fA ⟨x,hDA hx⟩) ∧
      (∀x (hx:x∉D),f x=fC ⟨x,hx⟩) ∧ (∀x y,G.Adj x y→H.Adj (f x) (f y)) := by
  classical
  let f:X→Y:=fun x=>if hx:x∈D then fA ⟨x,hDA hx⟩ else fC ⟨x,hx⟩
  have hf:Function.Injective f:=by
    intro x y hxy
    by_cases hx:x∈D <;> by_cases hy:y∈D
    · have h:fA ⟨x,hDA hx⟩=fA ⟨y,hDA hy⟩:=by simpa [f,hx,hy] using hxy
      exact congrArg Subtype.val (fA.injective h)
    · have h:fA ⟨x,hDA hx⟩=fC ⟨y,hy⟩:=by simpa [f,hx,hy] using hxy
      exact False.elim (hdis x hx y hy h)
    · have h:fA ⟨y,hDA hy⟩=fC ⟨x,hx⟩:=by simpa [f,hx,hy] using hxy.symm
      exact False.elim (hdis y hy x hx h)
    · have h:fC ⟨x,hx⟩=fC ⟨y,hy⟩:=by simpa [f,hx,hy] using hxy
      exact congrArg Subtype.val (fC.injective h)
  refine ⟨⟨f,hf⟩,?_,?_,?_⟩
  · intro x hx; simp [f,hx]
  · intro x hx; simp [f,hx]
  · intro x y hxy
    by_cases hx:x∈D <;> by_cases hy:y∈D
    · simpa [f,hx,hy] using hA x y (hDA hx) (hDA hy) hxy
    · have hyA:=hneigh x hx y hxy
      have h:=hA x y (hDA hx) hyA hxy
      rw [hbound y hyA hy] at h
      simpa [f,hx,hy] using h
    · have hxA:=hneigh y hy x hxy.symm
      have h:=hA y x (hDA hy) hxA hxy.symm
      rw [hbound x hxA hx] at h
      simpa [f,hx,hy] using h.symm
    · simpa [f,hx,hy] using hC x y hx hy hxy
end Oberwolfach
