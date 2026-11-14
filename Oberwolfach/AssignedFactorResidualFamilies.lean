module

public import Oberwolfach.FactorCycleReservedPathDisjoint
public import Oberwolfach.FactorOrientedCycleFamily
public import Oberwolfach.ActualResidualDataFromFamilies

@[expose] public section
/-! Assemble the original long reserved paths and assigned short factor
components into the actual residual-data families using one global orientation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem assigned_factor_residual_families
    {X A B J:Type} [Fintype X] [DecidableEq X] [Fintype A] [Fintype B] [Fintype J]
    [DecidableEq A] [DecidableEq B] [DecidableEq J]
    (F:SimpleGraph X) (hF:F.IsRegularOfDegree 2)
    (E:∀C:F.ConnectedComponent,SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph)
    (c d cutoff:ℕ) (pathComp:A⊕B→F.ConnectedComponent) (cycles:J↪F.ConnectedComponent)
    (hlong:∀i,cutoff≤Fintype.card (pathComp i)) (hshort:∀j,Fintype.card (cycles j)<cutoff)
    (ℓ:J→ℕ) (hsize:∀j,Fintype.card (cycles j)=ℓ j)
    (ext:∀i:A⊕B,Fin (c*d+5)↪X)
    (hext:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j)))
    (hcomponent:∀i k,ext i k∈(pathComp i).supp)
    (u v:A⊕B→X) (P:∀i,F.Walk (u i) (v i)) (hp:∀i,(P i).IsPath)
    (hsupp:∀i,(P i).support=List.ofFn (ext i)):
    (∀i j,i≠j→Disjoint (P i).support.toFinset (P j).support.toFinset) ∧
    ∃(root:J→X) (C:∀j,F.Walk (root j) (root j)),
      (∀j,(C j).IsCycle) ∧ (∀j,(C j).length=ℓ j) ∧
      (∀j k,k<(C j).length→factorCycleOrientation F E ((C j).getVert k)=(C j).getVert (k+1)) ∧
      (∀j,(C j).toSubgraph.verts=(cycles j).supp) ∧
      (∀i j,i≠j→Disjoint (C i).support.toFinset (C j).support.toFinset) ∧
      (∀i j,Disjoint (P i).support.toFinset (C j).support.toFinset):=by
  have hP:∀i j,i≠j→Disjoint (P i).support.toFinset (P j).support.toFinset:=by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hi:x∈Finset.univ.image (ext i):=by
      rw [hsupp i] at hx
      simpa only [List.mem_toFinset,List.mem_ofFn,Finset.mem_image,Finset.mem_univ,true_and] using hx
    have hj:x∈Finset.univ.image (ext j):=by
      rw [hsupp j] at hy
      simpa only [List.mem_toFinset,List.mem_ofFn,Finset.mem_image,Finset.mem_univ,true_and] using hy
    exact Finset.disjoint_left.mp (hext i j hij) hi hj
  refine ⟨hP,?_⟩
  obtain ⟨root,C,hC,hlenC,hdir,hcomp,hdis⟩:=factor_component_family_has_forward_cycles F hF E cycles
  have hcross:=factor_short_cycles_disjoint_from_long_reserved_paths F pathComp cycles cutoff hlong hshort
    (fun _=>c*d+5) (fun i=>ext i) u v P hsupp hcomponent root C hcomp
  exact ⟨root,C,hC,fun j=>(hlenC j).trans (hsize j),hdir,hcomp,hdis,hcross⟩
end Oberwolfach
