module

public import Oberwolfach.OrdinaryEmbeddedPackingHosts

@[expose] public section
/-! Change the spoke relation of a finite row packing when each actual wheel
survives and the designated root star is unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {Q F:SimpleGraph V} {H J:V→U→Prop} {r:ℕ}

def ordinaryWheelChangeSpokes (W:OrdinaryWheel Q F H r)
    (hW:∀v∈(ordinaryWheelRim W).support,J v (ordinaryWheelHub W)):OrdinaryWheel Q F J r:=
  ⟨W.val,hW,W.property.2⟩

def ordinarySpokeTransferPacking (M:Finset (OrdinaryWheel Q F H r))
    (hM:∀W∈M,∀v∈(ordinaryWheelRim W).support,J v (ordinaryWheelHub W)):
    Finset (OrdinaryWheel Q F J r):=
  M.attach.image (fun W=>ordinaryWheelChangeSpokes W.val (hM W.val W.property))

theorem ordinary_spoke_transfer_resources (M:Finset (OrdinaryWheel Q F H r))
    (hM:∀W∈M,∀v∈(ordinaryWheelRim W).support,J v (ordinaryWheelHub W)):
    (ordinarySpokeTransferPacking M hM).biUnion ordinaryWheelResources=M.biUnion ordinaryWheelResources:=by
  ext e
  simp only [Finset.mem_biUnion,ordinarySpokeTransferPacking,Finset.mem_image,Finset.mem_attach,true_and]
  constructor
  · rintro ⟨W,⟨Z,rfl⟩,h⟩;exact ⟨Z.val,Z.property,h⟩
  · rintro ⟨W,hW,h⟩;exact ⟨ordinaryWheelChangeSpokes W (hM W hW),⟨⟨W,hW⟩,rfl⟩,h⟩

theorem ordinary_spoke_transfer_row_cover (M:Finset (OrdinaryWheel Q F H r))
    (hM:∀W∈M,∀v∈(ordinaryWheelRim W).support,J v (ordinaryWheelHub W))
    (x:V) (A:Finset V) (K:ℕ) (hroot:∀u,H x u↔J x u) (hcover:OrdinaryRowCover M x A K):
    OrdinaryRowCover (ordinarySpokeTransferPacking M hM) x A K:=by
  let N:=ordinarySpokeTransferPacking M hM
  have he:N.biUnion ordinaryWheelResources=M.biUnion ordinaryWheelResources:=ordinary_spoke_transfer_resources M hM
  rw [ordinary_packing_resources_eq_host,ordinary_packing_resources_eq_host] at he
  have hrim:ordinaryWheelRimGraph N=ordinaryWheelRimGraph M:=by
    ext a b
    have hh:=congrArg (fun S:Finset (Sym2 V⊕(V×U))=>Sum.inl s(a,b)∈S) he
    simpa only [ordinaryHostResources_rim,SimpleGraph.mem_edgeSet] using (Iff.of_eq hh)
  have hspoke:ordinaryPackingSpokes N=ordinaryPackingSpokes M:=by
    funext a u;apply propext
    have hh:=congrArg (fun S:Finset (Sym2 V⊕(V×U))=>Sum.inr (a,u)∈S) he
    simpa only [ordinaryHostResources_spoke] using (Iff.of_eq hh)
  change OrdinaryRowCover N x A K
  constructor
  · intro W hW Z hZ hne
    obtain ⟨W',_,rfl⟩:=Finset.mem_image.mp hW
    obtain ⟨Z',_,rfl⟩:=Finset.mem_image.mp hZ
    apply hcover.disjoint W'.val W'.property Z'.val Z'.property
    intro heq
    apply hne
    apply Subtype.ext
    exact congrArg (fun W:OrdinaryWheel Q F H r=>W.val) heq
  · intro W hW a ha
    obtain ⟨W',_,rfl⟩:=Finset.mem_image.mp hW
    exact hcover.support W'.val W'.property a ha
  · rw [hrim];exact hcover.rims
  · intro u;rw [hspoke,hcover.spokes];exact hroot u
  · rw [hrim];exact hcover.rimDegree
  · rw [hspoke];exact hcover.rowDegree
  · rw [hspoke];exact hcover.columnDegree
end Oberwolfach
