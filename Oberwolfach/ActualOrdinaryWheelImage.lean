module

public import Oberwolfach.ActualOldPieceTargetSupport
public import Oberwolfach.PathFillsWheelRim

@[expose] public section
/-! Every vertex of a selected ordinary wheel lies in the old embedded
source image, including the closing vertex of the cycle. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_ordinary_wheel_rim_in_old_image
    {X V K J:Type} [Fintype X] [DecidableEq X] [DecidableEq V] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G) (hG:G.IsRegularOfDegree 2)
    (hCycle:data.t.biUnion (fun j=>(data.C j).support.toFinset)⊆data.Cembed)
    (u v:actualOldPieceIndex data→V) (q:∀z,(SimpleGraph.completeGraph V).Walk (u z) (v z))
    (hq:∀z,(q z).IsPath) (hlen:∀z,(q z).length=(actualOldPieceWalk data z).length)
    (f:{x // x∈(Finset.univ.biUnion (fun z:actualOldPieceIndex data=>(actualOldPieceWalk data z).support.toFinset))}↪V)
    (ψ:X→V)
    (hψf:∀x (hx:x∈(Finset.univ.biUnion (fun z:actualOldPieceIndex data=>(actualOldPieceWalk data z).support.toFinset))),ψ x=f ⟨x,hx⟩)
    (hf:∀z (k:Fin ((actualOldPieceWalk data z).length+1)),
      f ⟨(actualOldPieceWalk data z).getVert k.val,
        Finset.mem_biUnion.mpr ⟨z,Finset.mem_univ _,List.mem_toFinset.mpr ((actualOldPieceWalk data z).getVert_mem_support _)⟩⟩=(q z).getVert k.val)
    (lengths:{j // j∈data.t}→ℕ) (rim:∀j:{j // j∈data.t},Fin (lengths j+1)↪V)
    (hsize:∀j,(data.C j.val).length=lengths j+1)
    (hend:∀j,∃k:Fin (lengths j+1),v (.inl j)=rim j k)
    (hinner:∀j k,k<(q (.inl j)).length→∃a:Fin (lengths j+1),(q (.inl j)).getVert k=rim j a):
    ∀j k,rim j k∈(data.oldDomain\data.additionalSelectedInteriors).image ψ:=by
  have htarget:=actual_old_piece_target_support_in_old_image data hG hCycle u v q hq hlen f ψ hψf hf
  intro j k
  have htail:(data.C j.val).tail.length+1=(data.C j.val).length:=
    (data.C j.val).length_tail_add_one (data.hcycle j.val j.property).not_nil
  have hlen':(q (.inl j)).length=lengths j:=by
    have hh:=hlen (.inl j)
    change (q (.inl j)).length=(data.C j.val).tail.length at hh
    have hs:=hsize j
    omega
  have hEq:=simple_path_fills_wheel_rim (SimpleGraph.completeGraph V) (q (.inl j)) (hq (.inl j))
    (lengths j) hlen' (rim j) (hinner j) (hend j)
  have hmem:rim j k∈(q (.inl j)).support.toFinset:=by
    rw [hEq]
    exact Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩
  exact htarget (.inl j) hmem
end Oberwolfach
