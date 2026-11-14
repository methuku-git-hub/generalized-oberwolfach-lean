module

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

theorem ordinary_unreserved_walk_families
    {n:ℕ} {T J:Type} [Fintype T] [Fintype J]
    (F:SimpleGraph (Fin n)) (hF:F.IsRegularOfDegree 2) (Cres:Finset F.ConnectedComponent)
    (L:ℕ) (ext:∀i:T,Fin (L+1)↪Fin n)
    (P:∀i,(F.Walk (ext i 0) (ext i (Fin.last L))))
    (hp:∀i,(P i).IsPath) (hlen:∀i,(P i).length=L)
    (hsupp:∀i,(P i).support=List.ofFn (ext i))
    (havoid:∀i k,F.connectedComponentMk (ext i k)∉Cres)
    (root:J→Fin n) (C:∀j,F.Walk (root j) (root j)) (hcycle:∀j,(C j).IsCycle)
    (hcycleAvoid:∀j x,x∈(C j).support→F.connectedComponentMk x∉Cres):
    let S:Set (Fin n):={x | F.connectedComponentMk x∉Cres};
    ∃ext':∀i:T,Fin (L+1)↪S,
    ∃P':∀i,(F.induce S).Walk (ext' i 0) (ext' i (Fin.last L)),
      (∀i,(P' i).IsPath ∧ (P' i).length=L ∧ (P' i).support=List.ofFn (ext' i)) ∧
      (∀i k,(ext' i k).val=ext i k) ∧
    ∃root':J→S,∃C':∀j,(F.induce S).Walk (root' j) (root' j),
      (∀j,(C' j).IsCycle ∧ (C' j).length=(C j).length ∧ (C' j).support.map Subtype.val=(C j).support) ∧
      (∀j,(root' j).val=root j) :=by
  intro S
  have hPmem:∀i x,x∈(P i).support→x∈S:=by
    intro i x hx
    rw [hsupp i] at hx
    obtain ⟨k,hk⟩:=List.mem_ofFn.mp hx
    subst x
    exact havoid i k
  let ext':∀i:T,Fin (L+1)↪S:=fun i=>⟨fun k=>⟨ext i k,havoid i k⟩,by
    intro a b h
    exact (ext i).injective (congrArg Subtype.val h)⟩
  let P':∀i,(F.induce S).Walk (ext' i 0) (ext' i (Fin.last L)):=fun i=>(P i).induce S (hPmem i)
  have hall:=ordinary_unreserved_factor_paths F hF Cres
  have hP:∀i,(P' i).IsPath ∧ (P' i).length=L ∧ (P' i).support=List.ofFn (ext' i):=by
    intro i
    have hh:=hall.2.1 _ _ (P i) (hp i) (hPmem i)
    refine ⟨hh.2.1,hh.1.trans (hlen i),?_⟩
    apply (List.map_injective_iff.mpr Subtype.val_injective)
    rw [List.map_ofFn]
    change (P' i).support.map Subtype.val=List.ofFn (ext i)
    simpa only [hsupp i] using hh.2.2
  have hCmem:∀j x,x∈(C j).support→x∈S:=fun j x hx=>hcycleAvoid j x hx
  let root':J→S:=fun j=>⟨root j,hCmem j (root j) (C j).start_mem_support⟩
  let C':∀j,(F.induce S).Walk (root' j) (root' j):=fun j=>(C j).induce S (hCmem j)
  refine ⟨ext',P',hP,(fun _ _=>rfl),root',C',?_,fun _=>rfl⟩
  intro j
  have hh:=hall.2.2 _ (C j) (hcycle j) (hCmem j)
  exact ⟨hh.2.1,hh.1,hh.2.2⟩
end Oberwolfach
