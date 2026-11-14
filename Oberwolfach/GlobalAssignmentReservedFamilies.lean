module

public import Oberwolfach.AssignedComponentsAtHub
public import Oberwolfach.AssignedReservedSourceFamilies

@[expose] public section
/-! Restrict the globally injective assigned components to a single hub and
construct their cycles alongside that hub's original reserved source paths. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem global_assignment_reserved_source_families
    {U X I A B C:Type} [Fintype X] [DecidableEq X] [Fintype I] [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq U] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (F:U→SimpleGraph X) (hF:∀w,(F w).IsRegularOfDegree 2)
    (E:∀w (D:(F w).ConnectedComponent),SimpleGraph.cycleGraph (Fintype.card D) ≃g D.toSimpleGraph)
    (hub:C→U) (component:∀a,(F (hub a)).ConnectedComponent)
    (hinj:Function.Injective (fun a=>(⟨hub a,component a⟩:Σw,(F w).ConnectedComponent)))
    (ℓ:C→ℕ) (hsize:∀a,Fintype.card (component a)=ℓ a)
    (w:U) (components:I↪(F w).ConnectedComponent) (c d cutoff:ℕ)
    (hlong:∀i,cutoff≤Fintype.card (components i)) (hshort:∀a,ℓ a<cutoff)
    (hcapacity:Fintype.card (A⊕B)≤∑i:I,Fintype.card (components i)/(c*d+5)):
    let J:={a // hub a=w}
    let cycles:=assignedComponentsAtHub F hub component hinj w
    ∃(index:A⊕B↪LongReservedBlockIndex (F w) components c d)
      (ext:∀i:A⊕B,Fin (c*d+5)↪X) (inner:∀i:A⊕B,Fin (c*d+1)↪X),
      (∀i,ext i=longReservedSigmaBlock (F w) components c d (fun j=>E w (components j)) (index i) d (le_refl _)) ∧
      (∀i k,inner i k=ext i ⟨k.val+2,by omega⟩) ∧
      (∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j))) ∧
      ∃(P:∀i:A⊕B,(F w).Walk (ext i 0) (ext i (Fin.last (c*d+4)))) (root:J→X)
        (Cyc:∀j:J,(F w).Walk (root j) (root j)),
      (∀i,(P i).IsPath) ∧ (∀i,(P i).length=c*d+4) ∧ (∀i,(P i).support=List.ofFn (ext i)) ∧
      (∀i j,i≠j→Disjoint (P i).support.toFinset (P j).support.toFinset) ∧
      (∀j,(Cyc j).IsCycle) ∧ (∀j,(Cyc j).length=ℓ j.val) ∧
      (∀j k,k<(Cyc j).length→factorCycleOrientation (F w) (E w) ((Cyc j).getVert k)=(Cyc j).getVert (k+1)) ∧
      (∀j,(Cyc j).toSubgraph.verts=(cycles j).supp) ∧
      (∀i j,i≠j→Disjoint (Cyc i).support.toFinset (Cyc j).support.toFinset) ∧
      (∀i j,Disjoint (P i).support.toFinset (Cyc j).support.toFinset):=by
  intro J cycles
  have hc:∀j:J,Fintype.card (cycles j)=ℓ j.val:=by
    intro j
    exact (assigned_component_at_hub_card F hub component w j).trans (hsize j.val)
  have hs:∀j:J,Fintype.card (cycles j)<cutoff:=by intro j;rw [hc j];exact hshort j.val
  exact assigned_reserved_source_families (F w) (hF w) (E w) components cycles c d cutoff hlong hs
    (fun j=>ℓ j.val) hc hcapacity
end Oberwolfach
