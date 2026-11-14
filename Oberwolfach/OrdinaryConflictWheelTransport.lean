module

public import Oberwolfach.RowCoverUnion
public import Oberwolfach.InducedFractionalCycles

@[expose] public section

/-! Restore the full rim conflict graph after an endpoint construction.
The wheels, physical resources and all degrees remain exactly the same. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {Q F:SimpleGraph V} {H:V→U→Prop} {r:ℕ}

def ordinaryWheelOfConflictRestriction (Y:Finset V)
    (W:OrdinaryWheel Q (spanningRestriction F Y) H r)
    (hW:∀ v∈(ordinaryWheelRim W).support,v∈Y):OrdinaryWheel Q F H r:=
  ⟨W.val,W.property.1,fun v hv w hw hf=>W.property.2 v hv w hw
    ((spanningRestriction_adj F Y v w).mpr ⟨hf,hW v hv,hW w hw⟩)⟩

def ordinaryConflictPacking (Y:Finset V) (M:Finset (OrdinaryWheel Q (spanningRestriction F Y) H r))
    (hM:∀ W∈M,∀ v∈(ordinaryWheelRim W).support,v∈Y):Finset (OrdinaryWheel Q F H r):=
  M.attach.image (fun W=>ordinaryWheelOfConflictRestriction Y W.val (hM W.val W.property))

theorem ordinaryConflictPacking_rim (Y:Finset V) (M:Finset (OrdinaryWheel Q (spanningRestriction F Y) H r))
    (hM:∀ W∈M,∀ v∈(ordinaryWheelRim W).support,v∈Y):
    ordinaryWheelRimGraph (ordinaryConflictPacking Y M hM)=ordinaryWheelRimGraph M:=by
  ext a b
  simp only [ordinaryWheelRimGraph,ordinaryConflictPacking,SimpleGraph.iSup_adj,Finset.mem_image,Finset.mem_attach,true_and]
  constructor
  · rintro ⟨W,⟨Z,rfl⟩,h⟩
    exact ⟨Z.val,Z.property,h⟩
  · rintro ⟨W,hW,h⟩
    exact ⟨ordinaryWheelOfConflictRestriction Y W (hM W hW),⟨⟨W,hW⟩,rfl⟩,h⟩

theorem ordinaryConflictPacking_spokes (Y:Finset V) (M:Finset (OrdinaryWheel Q (spanningRestriction F Y) H r))
    (hM:∀ W∈M,∀ v∈(ordinaryWheelRim W).support,v∈Y):
    ordinaryPackingSpokes (ordinaryConflictPacking Y M hM)=ordinaryPackingSpokes M:=by
  funext a u
  apply propext
  simp only [ordinaryPackingSpokes,ordinaryConflictPacking,Finset.mem_image,Finset.mem_attach,true_and]
  constructor
  · rintro ⟨W,⟨Z,rfl⟩,hh,hv⟩
    exact ⟨Z.val,Z.property,hh,hv⟩
  · rintro ⟨W,hW,hh,hv⟩
    exact ⟨ordinaryWheelOfConflictRestriction Y W (hM W hW),⟨⟨W,hW⟩,rfl⟩,hh,hv⟩

theorem ordinaryConflictPacking_resources (Y:Finset V) (M:Finset (OrdinaryWheel Q (spanningRestriction F Y) H r))
    (hM:∀ W∈M,∀ v∈(ordinaryWheelRim W).support,v∈Y):
    (ordinaryConflictPacking Y M hM).biUnion ordinaryWheelResources=M.biUnion ordinaryWheelResources:=by
  ext e
  simp only [Finset.mem_biUnion,ordinaryConflictPacking,Finset.mem_image,Finset.mem_attach,true_and]
  constructor
  · rintro ⟨W,⟨Z,rfl⟩,h⟩
    exact ⟨Z.val,Z.property,h⟩
  · rintro ⟨W,hW,h⟩
    exact ⟨ordinaryWheelOfConflictRestriction Y W (hM W hW),⟨⟨W,hW⟩,rfl⟩,h⟩

theorem ordinaryRowCover_full_conflict (Y:Finset V) (M:Finset (OrdinaryWheel Q (spanningRestriction F Y) H r))
    (hM:∀ W∈M,∀ v∈(ordinaryWheelRim W).support,v∈Y) (x:V) (A:Finset V) (K:ℕ)
    (hcover:OrdinaryRowCover M x A K):OrdinaryRowCover (ordinaryConflictPacking Y M hM) x A K:=by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro W hW Z hZ hne
    obtain ⟨W',_,rfl⟩:=Finset.mem_image.mp hW
    obtain ⟨Z',_,rfl⟩:=Finset.mem_image.mp hZ
    apply hcover.disjoint W'.val W'.property Z'.val Z'.property
    intro he
    apply hne
    apply Subtype.ext
    exact congrArg (fun W:OrdinaryWheel Q (spanningRestriction F Y) H r=>W.val) he
  · intro W hW a ha
    obtain ⟨W',_,rfl⟩:=Finset.mem_image.mp hW
    exact hcover.support W'.val W'.property a ha
  · rw [ordinaryConflictPacking_rim]
    exact hcover.rims
  · rw [ordinaryConflictPacking_spokes]
    exact hcover.spokes
  · rw [ordinaryConflictPacking_rim]
    exact hcover.rimDegree
  · rw [ordinaryConflictPacking_spokes]
    exact hcover.rowDegree
  · rw [ordinaryConflictPacking_spokes]
    exact hcover.columnDegree

theorem ordinary_row_covers_full_conflict (Y Z:Finset V) (hZY:Z⊆Y) (n:ℕ) (x:Fin n→V)
    (hxY:∀ i,x i∈Y) (hxZ:∀ i,x i∉Z)
    (M:Fin n→Finset (OrdinaryWheel Q (spanningRestriction F Y) H r))
    (hc:∀ i,OrdinaryRowCover (M i) (x i) Z 0)
    (hcross:∀ i j,i≠j→Disjoint ((M i).biUnion ordinaryWheelResources) ((M j).biUnion ordinaryWheelResources)):
    ∃ M':Fin n→Finset (OrdinaryWheel Q F H r),
      (∀ i,OrdinaryRowCover (M' i) (x i) Z 0) ∧
      (∀ i j,i≠j→Disjoint ((M' i).biUnion ordinaryWheelResources) ((M' j).biUnion ordinaryWheelResources)) ∧
      (∀ a∈Z,(ordinaryWheelRimGraph (Finset.univ.biUnion M')).degree a≤2*n) ∧
      (∀ a∈Z,(Finset.univ.filter (ordinaryPackingSpokes (Finset.univ.biUnion M') a)).card≤n) ∧
      (∀ u,(Finset.univ.filter (fun a=>ordinaryPackingSpokes (Finset.univ.biUnion M') a u)).card≤r*n):=by
  have hs (i:Fin n):∀ W∈M i,∀ a∈(ordinaryWheelRim W).support,a∈Y:=by
    intro W hW a ha
    rcases (hc i).support W hW a ha with rfl|haZ
    · exact hxY i
    · exact hZY haZ
  let M':=fun i=>ordinaryConflictPacking Y (M i) (hs i)
  have hc' (i:Fin n):OrdinaryRowCover (M' i) (x i) Z 0:=ordinaryRowCover_full_conflict Y (M i) (hs i) (x i) Z 0 (hc i)
  have hbounds:=row_cover_union_degree_bounds M' x Z hxZ hc'
  refine ⟨M',hc',?_,?_,?_,?_⟩
  · intro i j hij
    dsimp [M']
    rw [ordinaryConflictPacking_resources,ordinaryConflictPacking_resources]
    exact hcross i j hij
  · simpa only [Nat.zero_add,Nat.mul_one,Nat.mul_comm] using hbounds.1
  · simpa only [Nat.zero_add,Nat.mul_one] using hbounds.2.1
  · simpa only [Nat.mul_comm] using hbounds.2.2

end Oberwolfach
