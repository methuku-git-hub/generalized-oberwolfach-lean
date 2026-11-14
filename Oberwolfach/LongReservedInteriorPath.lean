module

public import Oberwolfach.LongReservedSigmaBlocks

@[expose] public section
/-! Extract the requested interior path from its two-edge extension. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def longReservedInteriorEmbedding {V:Type*} (ℓ:ℕ) (f:Fin (ℓ+5)↪V):Fin (ℓ+1)↪V :=
  ({ toFun:=fun x:Fin (ℓ+1)=>⟨x.val+2,by omega⟩
     inj':=by intro x y h;apply Fin.ext;have hh:=congrArg Fin.val h;change x.val+2=y.val+2 at hh;omega } : Fin (ℓ+1)↪Fin (ℓ+5)).trans f

theorem long_reserved_interior_path
    {V:Type*} [Fintype V] [DecidableEq V] (G:SimpleGraph V) (ℓ:ℕ) (f:Fin (ℓ+5)↪V)
    (hadj:∀j:Fin (ℓ+4),G.Adj (f ⟨j.val,by omega⟩) (f ⟨j.val+1,by omega⟩)):
    let inner:=longReservedInteriorEmbedding ℓ f
    (∀j:Fin ℓ,G.Adj (inner ⟨j.val,by omega⟩) (inner ⟨j.val+1,by omega⟩)) ∧
    inner ⟨0,by omega⟩=f ⟨2,by omega⟩ ∧ inner ⟨ℓ,by omega⟩=f ⟨ℓ+2,by omega⟩ ∧
    Finset.univ.image inner ⊆ Finset.univ.image f := by
  intro inner
  refine ⟨?_,rfl,rfl,?_⟩
  · intro j
    change G.Adj (f ⟨j.val+2,by omega⟩) (f ⟨(j.val+1)+2,by omega⟩)
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hadj ⟨j.val+2,by omega⟩
  · intro x hx
    obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨⟨j.val+2,by omega⟩,Finset.mem_univ _,rfl⟩
end Oberwolfach
