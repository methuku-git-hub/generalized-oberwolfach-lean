module

public import Oberwolfach.AssignedFactorResidualFamilies
public import Oberwolfach.LongReservedPrescribedPaths
public import Oberwolfach.FiniteSequenceSimpleWalk

@[expose] public section
/-! Allocate the original buffered source paths and select the assigned short
cycles using the same global cyclic orders. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 26000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem assigned_reserved_source_families
    {X I A B J:Type} [Fintype X] [DecidableEq X] [Fintype I] [Fintype A] [Fintype B] [Fintype J]
    [DecidableEq A] [DecidableEq B] [DecidableEq J]
    (F:SimpleGraph X) (hF:F.IsRegularOfDegree 2)
    (E:∀C:F.ConnectedComponent,SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph)
    (components:I↪F.ConnectedComponent) (cycles:J↪F.ConnectedComponent)
    (c d cutoff:ℕ) (hlong:∀i,cutoff≤Fintype.card (components i))
    (hshort:∀j,Fintype.card (cycles j)<cutoff)
    (ℓ:J→ℕ) (hsize:∀j,Fintype.card (cycles j)=ℓ j)
    (hcapacity:Fintype.card (A⊕B)≤∑i:I,Fintype.card (components i)/(c*d+5)):
    ∃(index:A⊕B↪LongReservedBlockIndex F components c d)
      (ext:∀i:A⊕B,Fin (c*d+5)↪X) (inner:∀i:A⊕B,Fin (c*d+1)↪X),
      (∀i,ext i=longReservedSigmaBlock F components c d (fun j=>E (components j)) (index i) d (le_refl _)) ∧
      (∀i k,inner i k=ext i ⟨k.val+2,by omega⟩) ∧
      (∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j))) ∧
      ∃(P:∀i:A⊕B,F.Walk (ext i 0) (ext i (Fin.last (c*d+4)))) (root:J→X) (C:∀j,F.Walk (root j) (root j)),
      (∀i,(P i).IsPath) ∧ (∀i,(P i).length=c*d+4) ∧ (∀i,(P i).support=List.ofFn (ext i)) ∧
      (∀i j,i≠j→Disjoint (P i).support.toFinset (P j).support.toFinset) ∧
      (∀j,(C j).IsCycle) ∧ (∀j,(C j).length=ℓ j) ∧
      (∀j k,k<(C j).length→factorCycleOrientation F E ((C j).getVert k)=(C j).getVert (k+1)) ∧
      (∀j,(C j).toSubgraph.verts=(cycles j).supp) ∧
      (∀i j,i≠j→Disjoint (C i).support.toFinset (C j).support.toFinset) ∧
      (∀i j,Disjoint (P i).support.toFinset (C j).support.toFinset):=by
  obtain ⟨index,ext,inner,hext,hadj,hinner,_,hcomponent,hdis⟩:=
    long_reserved_prescribed_paths F hF components (fun j=>E (components j)) c d (fun _ : A⊕B=>d) (fun _=>le_refl _) hcapacity
  have hw:∀i:A⊕B,∃p:F.Walk (ext i 0) (ext i (Fin.last (c*d+4))),
      p.IsPath ∧ p.length=c*d+4 ∧ p.support=List.ofFn (ext i):=by
    intro i
    exact finite_sequence_simple_walk F (c*d+4) (ext i) (hadj i)
  choose P hp hlen hsupp using hw
  have hh:=assigned_factor_residual_families F hF E c d cutoff (fun i=>components (index i).1) cycles
    (fun i=>hlong (index i).1) hshort ℓ hsize ext hdis hcomponent _ _ P hp hsupp
  obtain ⟨hP,root,C,hcycle,hlenC,hdir,hcomp,hC,hcross⟩:=hh
  exact ⟨index,ext,inner,hext,hinner,hdis,P,root,C,hp,hlen,hsupp,hP,hcycle,hlenC,hdir,hcomp,hC,hcross⟩
end Oberwolfach
