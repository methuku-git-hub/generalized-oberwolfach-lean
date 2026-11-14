module

public import Oberwolfach.ActualBufferedFinalPathIdentification
public import Oberwolfach.ActualFinalPathEndpoints
public import Oberwolfach.BufferedMarkerAnchorEmbedding

@[expose] public section
/-! The matching's buffered marker labels automatically give the endpoint
labels needed when the residual and old embeddings are glued. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_buffered_final_endpoint_labels
    {X V I K J:Type} [Fintype X] [DecidableEq X] [Fintype I] [DecidableEq K] [DecidableEq J]
    {F:SimpleGraph X} (hF:F.IsRegularOfDegree 2) (data:ActualResidualData (K:=K) (J:=J) F)
    (ext:∀i:I,Fin (data.c*data.d+5)↪X) (inner:∀i:I,Fin (data.c*data.d+1)↪X)
    (hinner:∀i p,inner i p=ext i ⟨p.val+2,by omega⟩)
    (index:I→{i // i∈data.s₁})
    (hParent:∀i,(data.P (index i).val).support=List.ofFn (ext i))
    (π:Equiv.Perm V) (root:I→V) (ψ:X→V)
    (hmarker:∀i (j:Fin (data.d+1)),bufferedMarker data.c data.d (ext i) j∈data.prescribed→
      ψ (bufferedMarker data.c data.d (ext i) j)=(π^j.val) (root i)):
    (∀i,ψ (data.start (.inl (index i)))=root i) ∧
      (∀i,ψ (data.finish (.inl (index i)))=(π^data.d) (root i)):=by
  constructor
  · intro i
    have hp:=actual_final_path_matches_buffered_sequence data (index i) (ext i) (inner i) (hinner i) (hParent i)
    have he:bufferedMarker data.c data.d (ext i) 0=inner i 0:=by
      rw [hinner i 0]
      simp [bufferedMarker]
    have hmem:bufferedMarker data.c data.d (ext i) 0∈data.prescribed:=by
      rw [he,←hp.1]
      exact (actual_final_path_endpoints_prescribed data hF (index i)).1
    simpa only [he,←hp.1,Fin.val_zero,pow_zero,Equiv.Perm.one_apply] using hmarker i 0 hmem
  · intro i
    have hp:=actual_final_path_matches_buffered_sequence data (index i) (ext i) (inner i) (hinner i) (hParent i)
    have he:bufferedMarker data.c data.d (ext i) (Fin.last data.d)=inner i (Fin.last (data.c*data.d)):=by
      rw [hinner i (Fin.last (data.c*data.d))]
      unfold bufferedMarker
      congr 1
      apply Fin.ext
      simp
      omega
    have hmem:bufferedMarker data.c data.d (ext i) (Fin.last data.d)∈data.prescribed:=by
      rw [he,←hp.2.1]
      exact (actual_final_path_endpoints_prescribed data hF (index i)).2.1
    simpa only [he,←hp.2.1,Fin.val_last] using hmarker i (Fin.last data.d) hmem
end Oberwolfach
