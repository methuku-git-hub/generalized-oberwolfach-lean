module

public import Oberwolfach.LongReservedSimpleWalkEmbedding

@[expose] public section
/-! Reserved paths in components longer than K avoid all selected cycles in
components of length at most K. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_paths_disjoint_short_component_sets
    {X I J:Type*} [Fintype X] [DecidableEq X]
    (G:SimpleGraph X) (K:ℕ) (long:I→G.ConnectedComponent) (short:J→G.ConnectedComponent)
    (hLong:∀i,K<Fintype.card (long i)) (hShort:∀j,Fintype.card (short j)≤K)
    (len:I→ℕ) (ext:∀i,Fin (len i)↪X) (C:J→Finset X)
    (hExt:∀i p,ext i p∈(long i).supp)
    (hC:∀j x,x∈C j→x∈(short j).supp) :
    ∀i j,Disjoint (Finset.univ.image (ext i)) (C j) := by
  intro i j
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨p,_,rfl⟩:=Finset.mem_image.mp hx
  have heq:G.connectedComponentMk (ext i p)=long i:=
    (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp (hExt i p)
  have heq':G.connectedComponentMk (ext i p)=short j:=
    (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp (hC j (ext i p) hy)
  have hcomp:long i=short j:=heq.symm.trans heq'
  have hlarge:=hLong i
  rw [hcomp] at hlarge
  exact (not_lt_of_ge (hShort j)) hlarge
end Oberwolfach
