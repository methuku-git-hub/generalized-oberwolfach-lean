module

public import Oberwolfach.RowCoverPackings
public import Oberwolfach.NeighbourPairDomains

@[expose] public section

/-! Wheels on a fixed hub domain, embedded into the original host. The rim
is unchanged; each spoke retains its actual endpoint in the ambient hub set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {Q F:SimpleGraph V} {H:V→U→Prop} {r:ℕ}

def ordinaryWheelOfHubDomain (B:Finset U)
    (W:OrdinaryWheel Q F (fun v=>fun u:B=>H v u.val) r):OrdinaryWheel Q F H r:=
  ⟨(W.val.1,W.val.2.val),W.property⟩

theorem ordinaryWheelOfHubDomain_injective (B:Finset U):
    Function.Injective (ordinaryWheelOfHubDomain (Q:=Q) (F:=F) (H:=H) (r:=r) B):=by
  intro W Z he
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun W:OrdinaryWheel Q F H r=>W.val.1) he
  · apply Subtype.ext
    exact congrArg (fun W:OrdinaryWheel Q F H r=>W.val.2) he

def ordinaryHubDomainPacking (B:Finset U)
    (M:Finset (OrdinaryWheel Q F (fun v=>fun u:B=>H v u.val) r)):
    Finset (OrdinaryWheel Q F H r):=M.image (ordinaryWheelOfHubDomain B)

theorem ordinaryHubDomainPacking_rim (B:Finset U)
    (M:Finset (OrdinaryWheel Q F (fun v=>fun u:B=>H v u.val) r)):
    ordinaryWheelRimGraph (ordinaryHubDomainPacking B M)=ordinaryWheelRimGraph M:=by
  ext a b
  simp only [ordinaryWheelRimGraph,ordinaryHubDomainPacking,SimpleGraph.iSup_adj,Finset.mem_image]
  constructor
  · rintro ⟨W,⟨Z,hZ,rfl⟩,hab⟩;exact ⟨Z,hZ,hab⟩
  · rintro ⟨W,hW,hab⟩;exact ⟨ordinaryWheelOfHubDomain B W,⟨W,hW,rfl⟩,hab⟩

theorem ordinaryHubDomainPacking_spokes (B:Finset U)
    (M:Finset (OrdinaryWheel Q F (fun v=>fun u:B=>H v u.val) r)) (v:V) (u:U):
    ordinaryPackingSpokes (ordinaryHubDomainPacking B M) v u ↔
      ∃ hu:u∈B,ordinaryPackingSpokes M v ⟨u,hu⟩:=by
  simp only [ordinaryPackingSpokes,ordinaryHubDomainPacking,Finset.mem_image]
  constructor
  · rintro ⟨W,⟨Z,hZ,rfl⟩,he,hv⟩
    have hu:u∈B:=he ▸ Z.val.2.property
    exact ⟨hu,Z,hZ,Subtype.ext he,hv⟩
  · rintro ⟨hu,W,hW,he,hv⟩
    exact ⟨ordinaryWheelOfHubDomain B W,⟨W,hW,rfl⟩,congrArg Subtype.val he,hv⟩

theorem ordinaryHubDomainPacking_row_card (B:Finset U)
    (M:Finset (OrdinaryWheel Q F (fun v=>fun u:B=>H v u.val) r)) (v:V):
    (Finset.univ.filter (ordinaryPackingSpokes (ordinaryHubDomainPacking B M) v)).card=
      (Finset.univ.filter (ordinaryPackingSpokes M v)).card:=by
  let e:B↪U:=⟨Subtype.val,Subtype.val_injective⟩
  have he:(Finset.univ.filter (ordinaryPackingSpokes M v)).map e=
      Finset.univ.filter (ordinaryPackingSpokes (ordinaryHubDomainPacking B M) v):=by
    ext u
    simp only [Finset.mem_map,Finset.mem_filter,Finset.mem_univ,true_and,ordinaryHubDomainPacking_spokes]
    constructor
    · rintro ⟨w,hw,rfl⟩;exact ⟨w.property,hw⟩
    · rintro ⟨hu,hw⟩;exact ⟨⟨u,hu⟩,hw,rfl⟩
  rw [←he,Finset.card_map]

theorem ordinaryHubDomainPacking_column_card (B:Finset U)
    (M:Finset (OrdinaryWheel Q F (fun v=>fun u:B=>H v u.val) r)) (u:B):
    (Finset.univ.filter (fun v=>ordinaryPackingSpokes (ordinaryHubDomainPacking B M) v u.val)).card=
      (Finset.univ.filter (fun v=>ordinaryPackingSpokes M v u)).card:=by
  congr 1
  ext v
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,ordinaryHubDomainPacking_spokes]
  constructor
  · rintro ⟨hu,hv⟩;exact hv
  · intro hv;exact ⟨u.property,hv⟩

theorem ordinaryHubDomainPacking_column_empty (B:Finset U)
    (M:Finset (OrdinaryWheel Q F (fun v=>fun u:B=>H v u.val) r)) (u:U) (hu:u∉B):
    (Finset.univ.filter (fun v=>ordinaryPackingSpokes (ordinaryHubDomainPacking B M) v u))=∅:=by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  exact hu ((ordinaryHubDomainPacking_spokes B M v u).mp (Finset.mem_filter.mp hv).2).choose

theorem ordinaryWheelOfHubDomain_disjoint (B:Finset U)
    (W Z:OrdinaryWheel Q F (fun v=>fun u:B=>H v u.val) r)
    (h:Disjoint (ordinaryWheelResources W) (ordinaryWheelResources Z)):
    Disjoint (ordinaryWheelResources (ordinaryWheelOfHubDomain B W))
      (ordinaryWheelResources (ordinaryWheelOfHubDomain B Z)):=by
  apply Finset.disjoint_left.mpr
  intro e he hf
  cases e with
  | inl e=>
    exact Finset.disjoint_left.mp h
      ((ordinaryWheelResources_rim W e).mpr ((ordinaryWheelResources_rim (ordinaryWheelOfHubDomain B W) e).mp he))
      ((ordinaryWheelResources_rim Z e).mpr ((ordinaryWheelResources_rim (ordinaryWheelOfHubDomain B Z) e).mp hf))
  | inr vu=>
    obtain ⟨hw,hv⟩:=(ordinaryWheelResources_spoke _ vu.1 vu.2).mp he
    obtain ⟨hz,hv'⟩:=(ordinaryWheelResources_spoke _ vu.1 vu.2).mp hf
    have hu:ordinaryWheelHub W=ordinaryWheelHub Z:=Subtype.ext (hw.trans hz.symm)
    exact Finset.disjoint_left.mp h
      ((ordinaryWheelResources_spoke W vu.1 (ordinaryWheelHub W)).mpr ⟨rfl,hv⟩)
      ((ordinaryWheelResources_spoke Z vu.1 (ordinaryWheelHub W)).mpr ⟨hu.symm,hv'⟩)

theorem ordinaryHubDomainPacking_disjoint (B:Finset U)
    (M N:Finset (OrdinaryWheel Q F (fun v=>fun u:B=>H v u.val) r))
    (h:Disjoint (M.biUnion ordinaryWheelResources) (N.biUnion ordinaryWheelResources)):
    Disjoint ((ordinaryHubDomainPacking B M).biUnion ordinaryWheelResources)
      ((ordinaryHubDomainPacking B N).biUnion ordinaryWheelResources):=by
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨W,hW,he⟩:=Finset.mem_biUnion.mp he
  obtain ⟨Z,hZ,hf⟩:=Finset.mem_biUnion.mp hf
  obtain ⟨W,hWmem,rfl⟩:=Finset.mem_image.mp hW
  obtain ⟨Z,hZmem,rfl⟩:=Finset.mem_image.mp hZ
  have hd:Disjoint (ordinaryWheelResources W) (ordinaryWheelResources Z):=
    h.mono (Finset.subset_biUnion_of_mem ordinaryWheelResources hWmem)
      (Finset.subset_biUnion_of_mem ordinaryWheelResources hZmem)
  exact Finset.disjoint_left.mp (ordinaryWheelOfHubDomain_disjoint B W Z hd) he hf

theorem ordinaryHubDomainPacking_biUnion {n:ℕ} (B:Finset U)
    (C:Fin n→Finset (OrdinaryWheel Q F (fun v=>fun u:B=>H v u.val) r)):
    Finset.univ.biUnion (fun i=>ordinaryHubDomainPacking B (C i))=
      ordinaryHubDomainPacking B (Finset.univ.biUnion C):=by
  ext W
  simp only [ordinaryHubDomainPacking,Finset.mem_biUnion,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,Z,hZ,he⟩;exact ⟨Z,⟨i,hZ⟩,he⟩
  · rintro ⟨Z,⟨i,hZ⟩,he⟩;exact ⟨i,Z,hZ,he⟩

theorem ordinaryRowCover_of_hub_domain (B:Finset U)
    (M:Finset (OrdinaryWheel Q F (fun v=>fun u:B=>H v u.val) r)) (x:V) (A:Finset V) (K:ℕ)
    (h:OrdinaryRowCover M x A K) (hx:∀ u,H x u→u∈B):
    OrdinaryRowCover (ordinaryHubDomainPacking B M) x A K:=by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro W hW Z hZ hne
    obtain ⟨W,hWmem,rfl⟩:=Finset.mem_image.mp hW
    obtain ⟨Z,hZmem,rfl⟩:=Finset.mem_image.mp hZ
    exact ordinaryWheelOfHubDomain_disjoint B W Z
      (h.disjoint W hWmem Z hZmem (fun he=>hne (congrArg (ordinaryWheelOfHubDomain B) he)))
  · intro W hW a ha
    obtain ⟨W,hWmem,rfl⟩:=Finset.mem_image.mp hW
    exact h.support W hWmem a ha
  · simpa only [ordinaryHubDomainPacking_rim] using h.rims
  · intro u
    rw [ordinaryHubDomainPacking_spokes]
    constructor
    · rintro ⟨hu,hh⟩;exact (h.spokes ⟨u,hu⟩).mp hh
    · intro hh;exact ⟨hx u hh,(h.spokes ⟨u,hx u hh⟩).mpr hh⟩
  · intro a ha
    have he:=ordinaryHubDomainPacking_rim B M
    convert h.rimDegree a ha using 1 <;> rw [he]
  · intro a ha
    rw [ordinaryHubDomainPacking_row_card]
    exact h.rowDegree a ha
  · intro u
    by_cases hu:u∈B
    · rw [ordinaryHubDomainPacking_column_card B M ⟨u,hu⟩]
      exact h.columnDegree ⟨u,hu⟩
    · rw [ordinaryHubDomainPacking_column_empty B M u hu,Finset.card_empty]
      exact Nat.zero_le _

end Oberwolfach
