module

public import Oberwolfach.BufferedInitialEndpointGeometry
public import Oberwolfach.BufferedResidualSpokeCardinality
public import Oberwolfach.BufferedEndpointOutsideImageDisjoint

@[expose] public section
/-! Both initial and final endpoint images avoid the outside-path image of
the same injective complement embedding. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def bufferedInitialEndpointInComplement {X I:Type*} [Fintype I] [DecidableEq X]
    (n:I→ℕ) (ext:∀i,Fin (n i+5)↪X) (inner:∀i,Fin (n i+1)↪X)
    (hinner:∀i p,inner i p=ext i ⟨p.val+2,by omega⟩)
    (hdis:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j))) (i:I) :
    {x // x∉bufferedPathStrictInterior n inner} :=
  ⟨inner i 0,fun hx=>
    Finset.disjoint_left.mp (buffered_initial_endpoints_disjoint_strict n ext inner hinner hdis)
      (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩) hx⟩

theorem buffered_outside_image_avoids_both_endpoints
    {X V I:Type*} [Fintype X] [DecidableEq X] [DecidableEq V] [Fintype I]
    (n:I→ℕ) (ext:∀i,Fin (n i+5)↪X) (inner:∀i,Fin (n i+1)↪X)
    (hinner:∀i p,inner i p=ext i ⟨p.val+2,by omega⟩)
    (hdis:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j)))
    (fC:{x // x∉bufferedPathStrictInterior n inner}↪V)
    (start finish:I→V)
    (hstart:∀i,fC (bufferedInitialEndpointInComplement n ext inner hinner hdis i)=start i)
    (hfinish:∀i,fC (bufferedEndpointInComplement n ext inner hinner hdis i)=finish i):
    Disjoint (outsideBufferedPathImage n inner fC) (Finset.univ.image start) ∧
    Disjoint (outsideBufferedPathImage n inner fC) (Finset.univ.image finish):=by
  have hi:∀i,inner i 0∉bufferedPathStrictInterior n inner:=
    fun i=>(bufferedInitialEndpointInComplement n ext inner hinner hdis i).property
  have hf:∀i,inner i (Fin.last (n i))∉bufferedPathStrictInterior n inner:=
    fun i=>(bufferedEndpointInComplement n ext inner hinner hdis i).property
  constructor
  · apply buffered_outside_image_disjoint_endpoints n inner fC (fun i=>inner i 0)
      (fun i=>buffered_path_vertex_mem_domain n inner i 0) hi start
    exact hstart
  · apply buffered_outside_image_disjoint_endpoints n inner fC (fun i=>inner i (Fin.last (n i)))
      (fun i=>buffered_path_vertex_mem_domain n inner i (Fin.last (n i))) hf finish
    exact hfinish
end Oberwolfach
