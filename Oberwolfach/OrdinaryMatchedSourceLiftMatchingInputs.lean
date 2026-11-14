module

public import Oberwolfach.BufferedWalkImageDisjoint
public import Oberwolfach.OrdinarySourcePiecesAvoidReserved
public import Oberwolfach.OrdinaryUnreservedBufferedWalks
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

theorem ordinary_matched_source_lift_matching_inputs
    {n:ℕ} {A B J:Type} [Fintype A] [Fintype B] [Fintype J]
    (F:SimpleGraph (Fin n)) (hF:F.IsRegularOfDegree 2) (Cres:Finset F.ConnectedComponent)
    {K:ℕ} (i₀:Fin K) (hCres:∀Q,Q∈Cres→Fintype.card Q=i₀.val+1)
    (assign:J↪↥(Finset.univ\Cres))
    (c d:ℕ) (E:∀Q:F.ConnectedComponent,SimpleGraph.cycleGraph (Fintype.card Q) ≃g Q.toSimpleGraph)
    (block:A⊕B↪LongReservedBlockIndex F (Function.Embedding.subtype (fun Q:F.ConnectedComponent=>K<Fintype.card Q)) c d)
    (ext:∀i:A⊕B,Fin (c*d+5)↪Fin n)
    (hext:∀i,ext i=longReservedSigmaBlock F (Function.Embedding.subtype (fun Q:F.ConnectedComponent=>K<Fintype.card Q)) c d
      (fun j=>E j.val) (block i) d le_rfl)
    (P:∀i,F.Walk (ext i 0) (ext i (Fin.last (c*d+4))))
    (hp:∀i,(P i).IsPath) (hlen:∀i,(P i).length=c*d+4)
    (hsupp:∀i,(P i).support=List.ofFn (ext i))
    (inner:∀a:A,Fin (c*d+1)↪Fin n) (hinner:∀a k,inner a k=ext (.inl a) ⟨k.val+2,by omega⟩)
    (root:J→Fin n) (C:∀j,F.Walk (root j) (root j)) (hcycle:∀j,(C j).IsCycle)
    (hverts:∀j,(C j).toSubgraph.verts=(assign j).val.supp)
    (hPdis:∀i j,i≠j→Disjoint (P i).support.toFinset (P j).support.toFinset)
    (hCdis:∀i j,i≠j→Disjoint (C i).support.toFinset (C j).support.toFinset)
    (hcross:∀i j,Disjoint (P i).support.toFinset (C j).support.toFinset):
    let S:Set (Fin n):={x | F.connectedComponentMk x∉Cres};
    (F.induce S).IsRegularOfDegree 2 ∧
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
      (∀a k,(inner' a k).val=inner a k) ∧
      (∀i j,i≠j→Disjoint (Finset.univ.image (ext' i)) (Finset.univ.image (ext' j))) :=by
  intro S
  have hAvoid:=ordinary_source_pieces_avoid_reserved F i₀ Cres hCres assign c d E block
  have hpathAvoid:∀i k,F.connectedComponentMk (ext i k)∉Cres:=by
    intro i k
    rw [hext i]
    exact hAvoid.1 i k
  have hcycleAvoid:∀j x,x∈(C j).support→F.connectedComponentMk x∉Cres:=by
    intro j x hx
    have hx':x∈(C j).toSubgraph.verts:=(C j).mem_verts_toSubgraph.mpr hx
    rw [hverts j] at hx'
    exact hAvoid.2 j x hx'
  obtain ⟨ext',P',hP,hExt,root',C',hC,hRoot,hP',hC',hCross',inner',hInner',hVal⟩:=
    ordinary_unreserved_buffered_walks F hF Cres c d ext P hp hlen hsupp hpathAvoid inner hinner root C hcycle hcycleAvoid hPdis hCdis hcross
  have hreg: (F.induce S).IsRegularOfDegree 2:=(ordinary_unreserved_factor_paths F hF Cres).1
  have hSrc:=buffered_walk_images_disjoint (F.induce S) (c*d) ext' P' (fun i=>(hP i).2.2) hP'
  exact ⟨hreg,ext',P',hP,hExt,root',C',hC,hRoot,hP',hC',hCross',inner',hInner',hVal,hSrc⟩
end Oberwolfach
