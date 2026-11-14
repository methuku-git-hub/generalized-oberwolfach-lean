module

public import Oberwolfach.ActualFinalEndpointAgreement
public import Oberwolfach.ActualBufferedFinalPathIdentification
public import Oberwolfach.ActualResidualSumIndices
public import Oberwolfach.BufferedMarkerAnchorEmbedding

@[expose] public section
/-! Match the endpoints of the complement embedding to the retained roots
using the marker equations already present in the aligned source. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_sum_buffered_endpoint_agreement
    {X V A B J:Type} [Fintype X] [DecidableEq X] [DecidableEq V]
    [Fintype A] [DecidableEq A] [DecidableEq B] [DecidableEq J]
    {F:SimpleGraph X} (hF:F.IsRegularOfDegree 2) (data:ActualResidualData (K:=A⊕B) (J:=J) F)
    (c d:ℕ) (hc:data.c=c) (hd:data.d=d) (hs:data.s₁=firstSumIndices)
    (ext:∀i:A⊕B,Fin (c*d+5)↪X) (inner:∀a:A,Fin (c*d+1)↪X)
    (hsupp:∀i,(data.P i).support=List.ofFn (ext i))
    (hinner:∀a k,inner a k=ext (.inl a) ⟨k.val+2,by omega⟩)
    (hdis:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j)))
    (π:Equiv.Perm V) (root:A→V) (ψ:X→V)
    (hmarker:∀a (j:Fin (d+1)),bufferedMarker c d (ext (.inl a)) j∈data.prescribed→
      ψ (bufferedMarker c d (ext (.inl a)) j)=(π^j.val) (root a))
    (fC:{x // x∉bufferedPathStrictInterior (fun _:A=>c*d) inner}↪V)
    (hold:∀(x:{x // x∉bufferedPathStrictInterior (fun _:A=>c*d) inner}),x.val∈data.oldDomain→fC x=ψ x.val):
    let extA:=fun a:A=>ext (.inl a)
    let hdisA:∀i j,i≠j→Disjoint (Finset.univ.image (extA i)) (Finset.univ.image (extA j)):=
      fun i j hij=>hdis (.inl i) (.inl j) (by simpa using hij)
    (∀i,fC (bufferedInitialEndpointInComplement (fun _:A=>c*d) extA inner hinner hdisA i)=root i) ∧
    (∀i,fC (bufferedEndpointInComplement (fun _:A=>c*d) extA inner hinner hdisA i)=(π^d) (root i)):=by
  subst c
  subst d
  intro extA hdisA
  let ix (a:A):{i // i∈data.s₁}:=⟨.inl a,by rw [hs];simp [firstSumIndices]⟩
  have hpaths (a:A):=actual_final_path_matches_buffered_sequence data (ix a) (extA a) (inner a) (hinner a) (hsupp (.inl a))
  have hstart:∀a,ψ (data.start (.inl (ix a)))=root a:=by
    intro a
    have hp:bufferedMarker data.c data.d (extA a) 0∈data.prescribed:=by
      have ht:bufferedMarker data.c data.d (extA a) 0=data.start (.inl (ix a)):=by
        rw [(hpaths a).1,hinner];rfl
      rw [ht]
      exact (actual_final_path_endpoints_prescribed data hF (ix a)).1
    have ht:bufferedMarker data.c data.d (extA a) 0=data.start (.inl (ix a)):=by
      rw [(hpaths a).1,hinner];rfl
    have hh:=hmarker a 0 hp
    change ψ (bufferedMarker data.c data.d (extA a) 0)=(π^(0:ℕ)) (root a) at hh
    rw [ht] at hh
    simpa using hh
  have hfinish:∀a,ψ (data.finish (.inl (ix a)))=(π^data.d) (root a):=by
    intro a
    have ht:bufferedMarker data.c data.d (extA a) (Fin.last data.d)=data.finish (.inl (ix a)):=by
      rw [(hpaths a).2.1,hinner]
      dsimp only [extA,bufferedMarker]
      congr 1
      apply Fin.ext
      simp only [Fin.val_mk,Fin.val_last]
      omega
    have hp:bufferedMarker data.c data.d (extA a) (Fin.last data.d)∈data.prescribed:=by
      rw [ht]
      exact (actual_final_path_endpoints_prescribed data hF (ix a)).2.1
    have hh:=hmarker a (Fin.last data.d) hp
    change ψ (bufferedMarker data.c data.d (extA a) (Fin.last data.d))=(π^(Fin.last data.d).val) (root a) at hh
    rw [ht] at hh
    simpa only [Fin.val_last] using hh
  exact actual_final_endpoints_agree_with_complement data hF (fun _:A=>data.c*data.d) extA inner hinner hdisA ix
    (fun a=>(hpaths a).1) (fun a=>(hpaths a).2.1) fC ψ root (fun a=>(π^data.d) (root a)) hold hstart hfinish
end Oberwolfach
