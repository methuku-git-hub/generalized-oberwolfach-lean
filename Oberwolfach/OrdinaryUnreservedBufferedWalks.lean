module

public import Oberwolfach.OrdinaryUnreservedInnerLift

@[expose] public section
/-! Assemble the selected buffered walks, cycles and inner paths in the
unreserved factor, with their original disjointness and source vertices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_unreserved_buffered_walks
    {n:ℕ} {A B J:Type} [Fintype A] [Fintype B] [Fintype J]
    (F:SimpleGraph (Fin n)) (hF:F.IsRegularOfDegree 2) (Cres:Finset F.ConnectedComponent)
    (c d:ℕ) (ext:∀i:A⊕B,Fin (c*d+5)↪Fin n)
    (P:∀i,F.Walk (ext i 0) (ext i (Fin.last (c*d+4))))
    (hp:∀i,(P i).IsPath) (hlen:∀i,(P i).length=c*d+4)
    (hsupp:∀i,(P i).support=List.ofFn (ext i))
    (havoid:∀i k,F.connectedComponentMk (ext i k)∉Cres)
    (inner:∀a:A,Fin (c*d+1)↪Fin n) (hinner:∀a k,inner a k=ext (.inl a) ⟨k.val+2,by omega⟩)
    (root:J→Fin n) (C:∀j,F.Walk (root j) (root j)) (hcycle:∀j,(C j).IsCycle)
    (hcycleAvoid:∀j x,x∈(C j).support→F.connectedComponentMk x∉Cres)
    (hPdis:∀i j,i≠j→Disjoint (P i).support.toFinset (P j).support.toFinset)
    (hCdis:∀i j,i≠j→Disjoint (C i).support.toFinset (C j).support.toFinset)
    (hcross:∀i j,Disjoint (P i).support.toFinset (C j).support.toFinset):
    let S:Set (Fin n):={x | F.connectedComponentMk x∉Cres};
    ∃ext':∀i:A⊕B,Fin (c*d+5)↪S,
    ∃P':∀i,(F.induce S).Walk (ext' i 0) (ext' i (Fin.last (c*d+4))),
      (∀i,(P' i).IsPath ∧ (P' i).length=c*d+4 ∧ (P' i).support=List.ofFn (ext' i)) ∧
      (∀i k,(ext' i k).val=ext i k) ∧
    ∃root':J→S,∃C':∀j,(F.induce S).Walk (root' j) (root' j),
      (∀j,(C' j).IsCycle ∧ (C' j).length=(C j).length ∧ (C' j).support.map Subtype.val=(C j).support) ∧
      (∀j,(root' j).val=root j) ∧
      (∀i j,i≠j→Disjoint (P' i).support.toFinset (P' j).support.toFinset) ∧
      (∀i j,i≠j→Disjoint (C' i).support.toFinset (C' j).support.toFinset) ∧
      (∀i j,Disjoint (P' i).support.toFinset (C' j).support.toFinset) ∧
    ∃inner':∀a:A,Fin (c*d+1)↪S,
      (∀a k,inner' a k=ext' (.inl a) ⟨k.val+2,by omega⟩) ∧
      (∀a k,(inner' a k).val=inner a k) :=by
  intro S
  obtain ⟨ext',P',hP,hExt,root',C',hC,hRoot,hP',hC',hCross'⟩:=
    ordinary_unreserved_walk_families_disjoint F hF Cres (c*d+4) ext P hp hlen hsupp havoid root C hcycle hcycleAvoid hPdis hCdis hcross
  obtain ⟨inner',hInner',hVal⟩:=ordinary_unreserved_inner_lift S (c*d) ext inner hinner ext' hExt
  exact ⟨ext',P',hP,hExt,root',C',hC,hRoot,hP',hC',hCross',inner',hInner',hVal⟩
end Oberwolfach
