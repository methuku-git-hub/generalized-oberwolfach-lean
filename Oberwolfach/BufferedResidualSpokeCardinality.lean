module

public import Oberwolfach.ResidualSpokeCardinality
public import Oberwolfach.BufferedComplementImage
public import Oberwolfach.BufferedFinalEndpointGeometry
public import Oberwolfach.BufferedPathDomainCardinality
public import Oberwolfach.BufferedPathBoundaryCompletion

@[expose] public section
/-! Derive the residual-spoke cardinality from the actual buffered source
paths and the injective complement embedding, before path completion. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def bufferedEndpointInComplement {X I:Type*} [Fintype I] [DecidableEq X]
    (n:I→ℕ) (ext:∀i,Fin (n i+5)↪X) (inner:∀i,Fin (n i+1)↪X)
    (hinner:∀i p,inner i p=ext i ⟨p.val+2,by omega⟩)
    (hdis:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j))) (i:I) :
    {x // x∉bufferedPathStrictInterior n inner} :=
  ⟨inner i (Fin.last (n i)),fun hx=>
    Finset.disjoint_left.mp (buffered_final_endpoints_disjoint_strict n ext inner hinner hdis)
      (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩) hx⟩

theorem buffered_residual_spoke_card
    {X V I:Type*} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V] [Fintype I]
    (n:I→ℕ) (ext:∀i,Fin (n i+5)↪X) (inner:∀i,Fin (n i+1)↪X)
    (hinner:∀i p,inner i p=ext i ⟨p.val+2,by omega⟩)
    (hdis:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j)))
    (fC:{x // x∉bufferedPathStrictInterior n inner}↪V) (hcard:Fintype.card X=Fintype.card V)
    (finish:I→V) (hend:∀i,fC (bufferedEndpointInComplement n ext inner hinner hdis i)=finish i)
    (R:Finset V)
    (hR:R=Finset.univ\(outsideBufferedPathImage n inner fC ∪ Finset.univ.image finish)) :
    R.card=∑i,n i := by
  classical
  let A:=bufferedPathFullDomain n inner
  let D:=bufferedPathStrictInterior n inner
  let E:=bufferedFinalEndpoints n inner
  let hDA:D⊆A:=buffered_strict_interior_subset_domain n inner
  have hEA:E⊆A:=by
    intro x hx
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hx
    exact buffered_path_vertex_mem_domain n inner i (Fin.last (n i))
  have hED:Disjoint E D:=buffered_final_endpoints_disjoint_strict n ext inner hinner hdis
  let Z:=outsideBufferedPathImage n inner fC
  let B:=Finset.univ.image finish
  have hZ:Z=Finset.univ.image ((complementDomainEmbedding hDA).trans fC):=by
    ext v
    constructor
    · intro hv
      obtain ⟨x,hx,heq⟩:=Finset.mem_image.mp hv
      have hxA:x.val∉A:=(Finset.mem_filter.mp hx).2
      refine Finset.mem_image.mpr ⟨⟨x.val,hxA⟩,Finset.mem_univ _,?_⟩
      change fC ⟨x.val,_⟩=v
      exact heq
    · intro hv
      obtain ⟨x,_,heq⟩:=Finset.mem_image.mp hv
      let y:{x // x∉D}:=complementDomainEmbedding hDA x
      refine Finset.mem_image.mpr ⟨y,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
      · exact x.property
      · simpa [y,complementDomainEmbedding] using heq
  have hB:B=Finset.univ.image ((endpointDomainEmbedding hED).trans fC):=by
    ext v
    constructor
    · intro hv
      obtain ⟨i,_,heq⟩:=Finset.mem_image.mp hv
      let x:{x // x∈E}:=⟨inner i (Fin.last (n i)),Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
      refine Finset.mem_image.mpr ⟨x,Finset.mem_univ _,?_⟩
      change fC (endpointDomainEmbedding hED x)=v
      rw [←heq,←hend i]
      congr 1
    · intro hv
      obtain ⟨x,_,heq⟩:=Finset.mem_image.mp hv
      obtain ⟨i,_,hix⟩:=Finset.mem_image.mp x.property
      refine Finset.mem_image.mpr ⟨i,Finset.mem_univ _,?_⟩
      have hxi:bufferedEndpointInComplement n ext inner hinner hdis i=endpointDomainEmbedding hED x:=by
        apply Subtype.ext
        exact hix
      calc
        finish i = fC (bufferedEndpointInComplement n ext inner hinner hdis i):=(hend i).symm
        _ = fC (endpointDomainEmbedding hED x):=congrArg fC hxi
        _ = v:=heq
  have hcardR:=residual_spoke_card_from_complement_embedding A D E hDA hEA hED fC hcard R Z B hZ hB hR
  have hA:A.card=∑i,(n i+1):=by
    simpa [A,bufferedPathFullDomain] using buffered_path_interior_domain_card n ext inner hinner hdis Finset.univ
  have hE:E.card=Fintype.card I:=buffered_final_endpoints_card n ext inner hinner hdis
  have hsum:(∑i,(n i+1))=(∑i,n i)+Fintype.card I:=by simp [Finset.sum_add_distrib]
  rw [hcardR,hA,hE,hsum]
  omega
end Oberwolfach
