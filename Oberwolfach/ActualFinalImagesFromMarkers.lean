module

public import Oberwolfach.ActualFinalPathEndpoints
public import Oberwolfach.ActualBufferedFinalPathIdentification
public import Oberwolfach.BufferedMarkerAnchorEmbedding

@[expose] public section
/-! The marker map already built from the matching gives the two retained
endpoints, as well as the actual final-path support. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_final_images_from_buffered_markers
    {X V K J I:Type} [Fintype X] [DecidableEq X] [DecidableEq K] [DecidableEq J]
    {F:SimpleGraph X} (hF:F.IsRegularOfDegree 2)
    (data:ActualResidualData (K:=K) (J:=J) F)
    (b:I≃{i // i∈data.s₁}) (ext:∀i:I,Fin (data.c*data.d+5)↪X)
    (inner:∀i:I,Fin (data.c*data.d+1)↪X)
    (hinner:∀i p,inner i p=ext i ⟨p.val+2,by omega⟩)
    (hsupp:∀i,(data.P (b i).val).support=List.ofFn (ext i))
    (π:Equiv.Perm V) (root:K→V) (ψ:X→V)
    (hpres:∀i (j:Fin (data.d+1)),bufferedMarker data.c data.d (ext i) j∈data.prescribed→
      ψ (bufferedMarker data.c data.d (ext i) j)=(π^j.val) (root (b i).val)):
    (∀i,ψ (data.start (.inl (b i)))=root (b i).val) ∧
    (∀i,ψ (data.finish (.inl (b i)))=(π^data.d) (root (b i).val)) ∧
    (∀i,(data.path (.inl (b i))).support=List.ofFn (inner i)):=by
  have he:∀i,data.start (.inl (b i))=bufferedMarker data.c data.d (ext i) 0 ∧
      data.finish (.inl (b i))=bufferedMarker data.c data.d (ext i) (Fin.last data.d):=by
    intro i
    obtain ⟨hs,hf,_⟩:=actual_final_path_matches_buffered_sequence data (b i) (ext i) (inner i) (hinner i) (hsupp i)
    constructor
    · rw [hs,hinner]
      rfl
    · rw [hf,hinner]
      congr 1
      apply Fin.ext
      simp only [Fin.val_mk,Fin.val_last,bufferedMarker]
      omega
  refine ⟨?_,?_,?_⟩
  · intro i
    have hp:bufferedMarker data.c data.d (ext i) 0∈data.prescribed:=by
      rw [←(he i).1]
      exact (actual_final_path_endpoints_prescribed data hF (b i)).1
    rw [(he i).1]
    simpa using hpres i 0 hp
  · intro i
    have hp:bufferedMarker data.c data.d (ext i) (Fin.last data.d)∈data.prescribed:=by
      rw [←(he i).2]
      exact (actual_final_path_endpoints_prescribed data hF (b i)).2.1
    rw [(he i).2]
    simpa using hpres i (Fin.last data.d) hp
  · intro i
    exact (actual_final_path_matches_buffered_sequence data (b i) (ext i) (inner i) (hinner i) (hsupp i)).2.2
end Oberwolfach
