module

public import Oberwolfach.PermutationWindows

@[expose] public section
/-! Injective extended intervals with disjoint windows have globally injective
(parent, position) labels. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem disjoint_extended_orbit_labels_injective
    {V I:Type} [Fintype V] [DecidableEq V] (π:Equiv.Perm V) (d:ℕ) (root:I→V)
    (hinj:∀i,Function.Injective (fun j:Fin (d+1)=>(π^j.val) (root i)))
    (hdis:∀i j,i≠j→Disjoint (permutationWindow π 0 d (root i)) (permutationWindow π 0 d (root j))):
    Function.Injective (fun z:I×Fin (d+1)=>(π^z.2.val) (root z.1)):=by
  rintro ⟨i,j⟩ ⟨i',j'⟩ he
  change (π^j.val) (root i)=(π^j'.val) (root i') at he
  by_cases hi:i=i'
  · subst i'
    exact Prod.ext rfl (hinj i he)
  · have hleft:(π^j.val) (root i)∈permutationWindow π 0 d (root i):=by
      rw [permutationWindow_mem_iff]
      simp only [zero_add,pow_zero,Equiv.refl_apply]
      exact ⟨⟨j.val,by have hh:=j.isLt;omega⟩,rfl⟩
    have hright:(π^j.val) (root i)∈permutationWindow π 0 d (root i'):=by
      rw [he,permutationWindow_mem_iff]
      simp only [zero_add,pow_zero,Equiv.refl_apply]
      exact ⟨⟨j'.val,by have hh:=j'.isLt;omega⟩,rfl⟩
    exact False.elim (Finset.disjoint_left.mp (hdis i i' hi) hleft hright)
end Oberwolfach
