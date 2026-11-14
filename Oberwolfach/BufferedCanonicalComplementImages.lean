module

public import Oberwolfach.BufferedComplementImage
public import Oberwolfach.ResidualSpokeCardinality
public import Oberwolfach.BufferedPathBoundaryCompletion

@[expose] public section
/-! Identify the manuscript's outside-path and endpoint images with the
canonical subtype embeddings used by the oriented complement. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem outside_buffered_path_image_eq_canonical
    {X V I:Type*} [Fintype X] [DecidableEq X] [DecidableEq V] [Fintype I]
    (n:I→ℕ) (inner:∀i,Fin (n i+1)↪X)
    (fC:{x // x∉bufferedPathStrictInterior n inner}↪V):
    let hDA:=buffered_strict_interior_subset_domain n inner
    outsideBufferedPathImage n inner fC=
      Finset.univ.image ((complementDomainEmbedding hDA).trans fC):=by
  classical
  let A:=bufferedPathFullDomain n inner
  let D:=bufferedPathStrictInterior n inner
  let hDA:D⊆A:=buffered_strict_interior_subset_domain n inner
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

theorem endpoint_image_eq_canonical
    {X V I:Type*} [DecidableEq X] [DecidableEq V] [Fintype I]
    (D:Finset X) (e:I→X) (heD:∀i,e i∉D)
    (fC:{x // x∉D}↪V) (b:I→V) (hb:∀i,fC ⟨e i,heD i⟩=b i):
    let E:=Finset.univ.image e
    ∃hED:Disjoint E D,
      Finset.univ.image b=Finset.univ.image ((endpointDomainEmbedding hED).trans fC):=by
  classical
  let E:=Finset.univ.image e
  have hED:Disjoint E D:=by
    apply Finset.disjoint_left.mpr
    intro x hx hd
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hx
    exact heD i hd
  refine ⟨hED,?_⟩
  ext v
  constructor
  · intro hv
    obtain ⟨i,_,heq⟩:=Finset.mem_image.mp hv
    let x:{x // x∈E}:=⟨e i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
    refine Finset.mem_image.mpr ⟨x,Finset.mem_univ _,?_⟩
    change fC (endpointDomainEmbedding hED x)=v
    rw [←heq,←hb i]
    congr 1
  · intro hv
    obtain ⟨x,_,heq⟩:=Finset.mem_image.mp hv
    obtain ⟨i,_,hix⟩:=Finset.mem_image.mp x.property
    refine Finset.mem_image.mpr ⟨i,Finset.mem_univ _,?_⟩
    have hxi:(⟨e i,heD i⟩:{x // x∉D})=endpointDomainEmbedding hED x:=by
      apply Subtype.ext
      exact hix
    calc
      b i = fC ⟨e i,heD i⟩:=(hb i).symm
      _ = fC (endpointDomainEmbedding hED x):=congrArg fC hxi
      _ = v:=heq
end Oberwolfach
