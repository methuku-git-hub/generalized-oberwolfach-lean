module

public import Oberwolfach.OrdinaryUnreservedWalkDisjointness
public import Oberwolfach.OrdinaryUnreservedFactorPaths

@[expose] public section
/-! Lift the selected path and cycle families into the factor with whole
reserved components removed, keeping their exact source vertices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_unreserved_walk_families_disjoint
    {n:ℕ} {T J:Type} [Fintype T] [Fintype J]
    (F:SimpleGraph (Fin n)) (hF:F.IsRegularOfDegree 2) (Cres:Finset F.ConnectedComponent)
    (L:ℕ) (ext:∀i:T,Fin (L+1)↪Fin n)
    (P:∀i,(F.Walk (ext i 0) (ext i (Fin.last L))))
    (hp:∀i,(P i).IsPath) (hlen:∀i,(P i).length=L)
    (hsupp:∀i,(P i).support=List.ofFn (ext i))
    (havoid:∀i k,F.connectedComponentMk (ext i k)∉Cres)
    (root:J→Fin n) (C:∀j,F.Walk (root j) (root j)) (hcycle:∀j,(C j).IsCycle)
    (hcycleAvoid:∀j x,x∈(C j).support→F.connectedComponentMk x∉Cres)
    (hPdis:∀i j,i≠j→Disjoint (P i).support.toFinset (P j).support.toFinset)
    (hCdis:∀i j,i≠j→Disjoint (C i).support.toFinset (C j).support.toFinset)
    (hcross:∀i j,Disjoint (P i).support.toFinset (C j).support.toFinset):
    let S:Set (Fin n):={x | F.connectedComponentMk x∉Cres};
    ∃ext':∀i:T,Fin (L+1)↪S,
    ∃P':∀i,(F.induce S).Walk (ext' i 0) (ext' i (Fin.last L)),
      (∀i,(P' i).IsPath ∧ (P' i).length=L ∧ (P' i).support=List.ofFn (ext' i)) ∧
      (∀i k,(ext' i k).val=ext i k) ∧
    ∃root':J→S,∃C':∀j,(F.induce S).Walk (root' j) (root' j),
      (∀j,(C' j).IsCycle ∧ (C' j).length=(C j).length ∧ (C' j).support.map Subtype.val=(C j).support) ∧
      (∀j,(root' j).val=root j) ∧
      (∀i j,i≠j→Disjoint (P' i).support.toFinset (P' j).support.toFinset) ∧
      (∀i j,i≠j→Disjoint (C' i).support.toFinset (C' j).support.toFinset) ∧
      (∀i j,Disjoint (P' i).support.toFinset (C' j).support.toFinset) :=by
  intro S
  obtain ⟨ext',P',hP,hExt,root',C',hC,hRoot⟩:=
    ordinary_unreserved_walk_families F hF Cres L ext P hp hlen hsupp havoid root C hcycle hcycleAvoid
  have hPsupp:∀i,(P' i).support.map Subtype.val=(P i).support:=by
    intro i
    rw [(hP i).2.2,List.map_ofFn,hsupp i]
    congr 1
    funext k
    exact hExt i k
  have hCsupp:∀j,(C' j).support.map Subtype.val=(C j).support:=fun j=>(hC j).2.2
  have hdis:=ordinary_unreserved_walk_disjointness F S (fun i=>ext i 0) (fun i=>ext i (Fin.last L)) P root C
    (fun i=>ext' i 0) (fun i=>ext' i (Fin.last L)) P' root' C' hPsupp hCsupp hPdis hCdis hcross
  exact ⟨ext',P',hP,hExt,root',C',hC,hRoot,hdis⟩
end Oberwolfach
