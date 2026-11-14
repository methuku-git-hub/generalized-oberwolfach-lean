module

public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section
/-! Match two finite injective sequences by their common index. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem finite_index_range_embedding
    {V W I:Type*} [DecidableEq V] [Fintype I] (source:I↪V) (target:I↪W):
    ∃f:{x // x∈Finset.univ.image source}↪W,
      ∀k:I,f ⟨source k,Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩⟩=target k:=by
  classical
  let idx (x:{x // x∈Finset.univ.image source}):I:=Classical.choose (Finset.mem_image.mp x.property)
  have hidx (x:{x // x∈Finset.univ.image source}):source (idx x)=x.val:=
    (Classical.choose_spec (Finset.mem_image.mp x.property)).2
  let φ (x:{x // x∈Finset.univ.image source}):W:=target (idx x)
  have hinj:Function.Injective φ:=by
    intro x y hxy
    have hidxeq:idx x=idx y:=target.injective hxy
    apply Subtype.ext
    calc
      x.val=source (idx x):=(hidx x).symm
      _=source (idx y):=congrArg source hidxeq
      _=y.val:=hidx y
  refine ⟨⟨φ,hinj⟩,?_⟩
  intro k
  let x:{x // x∈Finset.univ.image source}:=⟨source k,Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩⟩
  change target (idx x)=target k
  congr 1
  apply source.injective
  exact hidx x
end Oberwolfach
