module

public import Oberwolfach.ActualFinalPathEndpoints
public import Oberwolfach.BufferedEndpointImagesAvoidOutside

@[expose] public section
/-! Agreement of the actual complement map with the prescribed endpoint
images of the selected final paths. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_final_endpoints_agree_with_complement
    {X V I K J:Type} [Fintype X] [DecidableEq X] [DecidableEq V] [Fintype I] [DecidableEq K] [DecidableEq J]
    {F:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) F) (hF:F.IsRegularOfDegree 2)
    (n:I→ℕ) (ext:∀i,Fin (n i+5)↪X) (inner:∀i,Fin (n i+1)↪X)
    (hinner:∀i p,inner i p=ext i ⟨p.val+2,by omega⟩)
    (hdis:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j)))
    (index:I→{i // i∈data.s₁})
    (hstart:∀i,data.start (.inl (index i))=inner i 0)
    (hfinish:∀i,data.finish (.inl (index i))=inner i (Fin.last (n i)))
    (fC:{x // x∉bufferedPathStrictInterior n inner}↪V) (ψ:X→V) (a b:I→V)
    (hold:∀(x:{x // x∉bufferedPathStrictInterior n inner}),x.val∈data.oldDomain→fC x=ψ x.val)
    (hψstart:∀i,ψ (data.start (.inl (index i)))=a i)
    (hψfinish:∀i,ψ (data.finish (.inl (index i)))=b i):
    (∀i,fC (bufferedInitialEndpointInComplement n ext inner hinner hdis i)=a i) ∧
    (∀i,fC (bufferedEndpointInComplement n ext inner hinner hdis i)=b i):=by
  constructor
  · intro i
    let x:=bufferedInitialEndpointInComplement n ext inner hinner hdis i
    have hx:x.val∈data.oldDomain:=by
      change inner i 0∈data.oldDomain
      rw [←hstart i]
      exact (actual_final_path_endpoints_prescribed data hF (index i)).2.2.1
    calc
      fC x=ψ x.val:=hold x hx
      _=a i:=by change ψ (inner i 0)=a i;rw [←hstart i];exact hψstart i
  · intro i
    let x:=bufferedEndpointInComplement n ext inner hinner hdis i
    have hx:x.val∈data.oldDomain:=by
      change inner i (Fin.last (n i))∈data.oldDomain
      rw [←hfinish i]
      exact (actual_final_path_endpoints_prescribed data hF (index i)).2.2.2.1
    calc
      fC x=ψ x.val:=hold x hx
      _=b i:=by change ψ (inner i (Fin.last (n i)))=b i;rw [←hfinish i];exact hψfinish i
end Oberwolfach
