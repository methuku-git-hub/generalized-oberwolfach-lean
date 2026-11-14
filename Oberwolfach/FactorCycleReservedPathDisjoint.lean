module

public import Oberwolfach.FactorOrientedCycleFamily

@[expose] public section
/-! Cycles chosen from components disjoint from those of the reserved parent
paths are disjoint from those paths. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem factor_component_cycles_disjoint_from_reserved_paths
    {X I J:Type} [Fintype X] [DecidableEq X]
    (G:SimpleGraph X) (pathComponent:I→G.ConnectedComponent) (cycleComponent:J→G.ConnectedComponent)
    (m:I→ℕ) (ext:∀i,Fin (m i)→X)
    (u v:I→X) (P:∀i,G.Walk (u i) (v i))
    (hpath:∀i,(P i).support=List.ofFn (ext i))
    (hpathComponent:∀i k,ext i k∈(pathComponent i).supp)
    (root:J→X) (C:∀j,G.Walk (root j) (root j))
    (hcycleComponent:∀j,(C j).toSubgraph.verts=(cycleComponent j).supp)
    (hseparate:∀i j,pathComponent i≠cycleComponent j):
    ∀i j,Disjoint (P i).support.toFinset (C j).support.toFinset:=by
  intro i j
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hx':x∈(pathComponent i).supp:=by
    have hh: x∈List.ofFn (ext i):=by simpa only [←hpath i] using List.mem_toFinset.mp hx
    obtain ⟨k,hk⟩:=List.mem_ofFn.mp hh
    rw [←hk]
    exact hpathComponent i k
  have hy':x∈(cycleComponent j).supp:=by
    rw [←hcycleComponent j]
    exact (C j).mem_verts_toSubgraph.mpr (List.mem_toFinset.mp hy)
  exact Set.disjoint_left.mp (G.pairwise_disjoint_supp_connectedComponent (hseparate i j)) hx' hy'
end Oberwolfach

namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem factor_short_cycles_disjoint_from_long_reserved_paths
    {X I J:Type} [Fintype X] [DecidableEq X]
    (G:SimpleGraph X) (pathComponent:I→G.ConnectedComponent) (cycleComponent:J→G.ConnectedComponent)
    (cutoff:ℕ) (hlong:∀i,cutoff≤Fintype.card (pathComponent i))
    (hshort:∀j,Fintype.card (cycleComponent j)<cutoff)
    (m:I→ℕ) (ext:∀i,Fin (m i)→X)
    (u v:I→X) (P:∀i,G.Walk (u i) (v i))
    (hpath:∀i,(P i).support=List.ofFn (ext i))
    (hpathComponent:∀i k,ext i k∈(pathComponent i).supp)
    (root:J→X) (C:∀j,G.Walk (root j) (root j))
    (hcycleComponent:∀j,(C j).toSubgraph.verts=(cycleComponent j).supp):
    ∀i j,Disjoint (P i).support.toFinset (C j).support.toFinset:=by
  apply factor_component_cycles_disjoint_from_reserved_paths G pathComponent cycleComponent m ext u v P hpath hpathComponent root C hcycleComponent
  intro i j h
  have hh:=hlong i
  rw [h] at hh
  have hh':=hshort j
  omega
end Oberwolfach
