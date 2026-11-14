module

public import Oberwolfach.ActualPrescribedBufferedMarkers

@[expose] public section
/-! Restrict the single buffered-marker map to the actual prescribed domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_prescribed_anchor_embedding
    {X V K J:Type} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V]
    [Fintype K] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G)
    (ext:∀i:K,Fin (data.c*data.d+5)↪X)
    (hsupp:∀i∈data.s₁∪data.s₂,(data.P i).support=List.ofFn (ext i))
    (hsrc:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j)))
    (π:Equiv.Perm V) (root:K→V)
    (hinj:∀i,Function.Injective (fun j:Fin (data.d+1)=>(π^j.val) (root i)))
    (htgt:∀i j,i≠j→Disjoint (permutationWindow π 0 data.d (root i)) (permutationWindow π 0 data.d (root j))):
    ∃g:{x // x∈data.prescribed}↪V,
      ∀i (j:Fin (data.d+1)) (hj:bufferedMarker data.c data.d (ext i) j∈data.prescribed),
        g ⟨bufferedMarker data.c data.d (ext i) j,hj⟩=(π^j.val) (root i):=by
  classical
  let A:=Finset.univ.image (fun z:K×Fin (data.d+1)=>bufferedMarker data.c data.d (ext z.1) z.2)
  have hsub:data.prescribed⊆A:=actual_prescribed_subset_buffered_markers data ext hsupp
  obtain ⟨f,hf⟩:=buffered_marker_anchor_embedding data.c data.d (lt_of_lt_of_le (by decide : 0<3) data.hc) ext hsrc π root hinj htgt
  let incl:{x // x∈data.prescribed}↪{x // x∈A}:=
    ⟨fun x=>⟨x.val,hsub x.property⟩,by intro x y h;apply Subtype.ext;exact congrArg (fun (z:{x // x∈A})=>z.val) h⟩
  refine ⟨incl.trans f,?_⟩
  intro i j hj
  change f ⟨bufferedMarker data.c data.d (ext i) j,_⟩=(π^j.val) (root i)
  exact hf i j
end Oberwolfach
