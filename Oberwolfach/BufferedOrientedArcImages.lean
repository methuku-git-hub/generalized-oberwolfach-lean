module

public import Oberwolfach.ComplementOrientedArcImages
public import Oberwolfach.BufferedCanonicalComplementImages
public import Oberwolfach.BufferedEndpointImagesAvoidOutside

@[expose] public section
/-! Construct the oriented complement embeddings and derive the exact
outside-path and endpoint image descriptions. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem buffered_oriented_arc_images
    {X V I:Type*} [Fintype X] [DecidableEq X] [DecidableEq V] [Fintype I]
    (n:I→ℕ) (ext:∀i,Fin (n i+5)↪X) (inner:∀i,Fin (n i+1)↪X)
    (hinner:∀i p,inner i p=ext i ⟨p.val+2,by omega⟩)
    (hdis:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j)))
    (σ:Equiv.Perm X)
    (hσ:(complementTailDomain (bufferedPathFullDomain n inner) (bufferedFinalEndpoints n inner)).image σ=
      complementTailDomain (bufferedPathFullDomain n inner) (bufferedInitialEndpoints n inner))
    (fC:{x // x∉bufferedPathStrictInterior n inner}↪V)
    (start finish:I→V)
    (hstart:∀i,fC (bufferedInitialEndpointInComplement n ext inner hinner hdis i)=start i)
    (hfinish:∀i,fC (bufferedEndpointInComplement n ext inner hinner hdis i)=finish i):
    ∃tail head:{x // x∈complementTailDomain (bufferedPathFullDomain n inner) (bufferedFinalEndpoints n inner)}↪V,
      Finset.univ.image tail=outsideBufferedPathImage n inner fC ∪ Finset.univ.image finish ∧
      Finset.univ.image head=outsideBufferedPathImage n inner fC ∪ Finset.univ.image start:=by
  classical
  let A:=bufferedPathFullDomain n inner
  let D:=bufferedPathStrictInterior n inner
  let B:=bufferedFinalEndpoints n inner
  let T:=bufferedInitialEndpoints n inner
  let hDA:D⊆A:=buffered_strict_interior_subset_domain n inner
  let hBD:Disjoint B D:=buffered_final_endpoints_disjoint_strict n ext inner hinner hdis
  let hTD:Disjoint T D:=buffered_initial_endpoints_disjoint_strict n ext inner hinner hdis
  let tail:=complementTailEmbedding A D B hDA hBD fC
  let head:=complementHeadEmbedding A D B T hDA hTD σ hσ fC
  refine ⟨tail,head,?_⟩
  have hZ:=outside_buffered_path_image_eq_canonical n inner fC
  have hni:∀i,inner i 0∉D:=fun i=>(bufferedInitialEndpointInComplement n ext inner hinner hdis i).property
  have hnf:∀i,inner i (Fin.last (n i))∉D:=fun i=>(bufferedEndpointInComplement n ext inner hinner hdis i).property
  obtain ⟨hTD',hT⟩:=endpoint_image_eq_canonical D (fun i=>inner i 0) hni fC start hstart
  obtain ⟨hBD',hB⟩:=endpoint_image_eq_canonical D (fun i=>inner i (Fin.last (n i))) hnf fC finish hfinish
  have h:=complement_oriented_arc_images A D B T hDA hBD hTD σ hσ fC
  change Finset.univ.image tail=outsideBufferedPathImage n inner fC∪Finset.univ.image finish ∧
    Finset.univ.image head=outsideBufferedPathImage n inner fC∪Finset.univ.image start
  rw [hZ,hB,hT]
  exact h
end Oberwolfach
