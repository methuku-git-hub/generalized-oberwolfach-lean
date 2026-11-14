module

public import Oberwolfach.ActualPrescribedBufferedMarkers

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_prescribed_marker_image_geometry
    {V K J:Type} [Fintype V] [DecidableEq V] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph V} (a:ActualResidualData (K:=K) (J:=J) G)
    (c d:ℕ) (hc:a.c=c) (hd:a.d=d)
    (ext:∀i:K,Fin (c*d+5)↪V) (ψ:V→V) (π:Equiv.Perm V) (root:K→V)
    (hsupp:∀i,(a.P i).support=List.ofFn (ext i))
    (hmarker:∀i (j:Fin (d+1)),bufferedMarker c d (ext i) j∈a.prescribed→
      ψ (bufferedMarker c d (ext i) j)=(π^j.val) (root i)):
    ∀i∈a.s₁∪a.s₂,∀j≤d,(a.P i).getVert (2+a.c*j)∈a.prescribed→
      ψ ((a.P i).getVert (2+a.c*j))=(π^j) (root i):=by
  intro i hi j hj hp
  have hm:=Nat.mul_le_mul_left c hj
  have hl:2+c*j≤(a.P i).length:=by rw [a.hlen i hi,hc,hd];omega
  have hh:some ((a.P i).getVert (2+c*j))=(a.P i).support[2+c*j]? := (a.P i).getVert_eq_support_getElem? hl
  rw [hsupp i] at hh
  have he:(a.P i).getVert (2+c*j)=bufferedMarker c d (ext i) ⟨j,by omega⟩:=by
    simpa only [List.getElem?_ofFn,dif_pos (show 2+c*j<c*d+5 by omega),Option.some.injEq,bufferedMarker] using hh
  rw [hc,he] at hp ⊢
  exact hmarker i ⟨j,by omega⟩ hp
end Oberwolfach
