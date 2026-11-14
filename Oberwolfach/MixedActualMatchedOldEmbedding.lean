module

public import Oberwolfach.MixedActualPrescribedAnchors
public import Oberwolfach.ActualAnchorRunEndpoints
public import Oberwolfach.ActualOldMatchedEndpointEmbedding

@[expose] public section
/-! Use one mixed outcome to construct the actual prescribed anchor map and
match the same selected source pieces; glue them when their remaining images
are disjoint. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem mixed_actual_matched_old_embedding
    {X V K J U Γ Color I:Type} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V] [Nonempty V]
    [Fintype K] [DecidableEq K] [DecidableEq J] [Fintype U] [DecidableEq U] [Fintype Γ] [DecidableEq Γ]
    [Fintype Color] [Fintype I]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G) (hG:G.IsRegularOfDegree 2)
    (hCycle:data.t.biUnion (fun j=>(data.C j).support.toFinset)⊆data.Cembed)
    (π:Equiv.Perm V) (hnoshort:∀x l,0<l→l<2*data.d+1→(π^l) x≠x)
    (σ:RawIntervalFamilyOutcome V U Γ Color) (g₀ g₁:Γ) (hclasses:g₀≠g₁) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π data.d σ g₀) t) (w:U)
    (index:K ≃ retainedAndRawIntervalIndex π data.d σ g₀ g₁ t Jret w)
    (ext:∀i:K,Fin (data.c*data.d+5)↪X)
    (hsupp:∀i∈data.s₁∪data.s₂,(data.P i).support=List.ofFn (ext i))
    (hsrc:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j)))
    (b:I≃{i // i∈data.s₁}) (finalExt:∀i:I,Fin (data.c*data.d+5)↪X)
    (inner:∀i:I,Fin (data.c*data.d+1)↪X)
    (hinner:∀i p,inner i p=finalExt i ⟨p.val+2,by omega⟩)
    (hfinal:∀i,(data.P (b i).val).support=List.ofFn (finalExt i))
    (H:SimpleGraph V) (u v:actualOldPieceIndex data→V)
    (q:∀z,H.Walk (u z) (v z)) (hq:∀z,(q z).IsPath)
    (hlen:∀z,(q z).length=(actualOldPieceWalk data z).length)
    (hqdis:∀z z',z≠z'→Disjoint (q z).support.toFinset (q z').support.toFinset):
    let root:=fun i=>retainedAndRawIntervalRoot π data.d σ g₀ g₁ t Jret w (index i)
    (∀r:SelectedRunIndex data.s₂ data.d data.T,u (.inr r)=(π^r.2.val.1) (root r.1.val))→
    (∀r:SelectedRunIndex data.s₂ data.d data.T,v (.inr r)=(π^(r.2.val.2+1)) (root r.1.val))→
    let A:=Finset.univ.biUnion (fun z:actualOldPieceIndex data=>(actualOldPieceWalk data z).support.toFinset)
    ∃(g:{x // x∈data.prescribed}↪V) (f:{x // x∈A}↪V),
      (∀i (j:Fin (data.d+1)) (hj:bufferedMarker data.c data.d (ext i) j∈data.prescribed),
        g ⟨bufferedMarker data.c data.d (ext i) j,hj⟩=(π^j.val) (root i)) ∧
      (∀z (k:Fin ((actualOldPieceWalk data z).length+1)),
        f ⟨(actualOldPieceWalk data z).getVert k.val,
          Finset.mem_biUnion.mpr ⟨z,Finset.mem_univ _,List.mem_toFinset.mpr ((actualOldPieceWalk data z).getVert_mem_support _)⟩⟩=
          (q z).getVert k.val) ∧
      ((∀x (hx:x∈data.prescribed) (hxa:x∉A) (y:{x // x∈A}),g ⟨x,hx⟩≠f y)→
        ∃ψ:X→V,Set.InjOn ψ (↑(data.oldDomain\bufferedPathStrictInterior (fun _=>data.c*data.d) inner):Set X) ∧
          (∀x (hx:x∈A),ψ x=f ⟨x,hx⟩) ∧ (∀x (hx:x∈data.prescribed),ψ x=g ⟨x,hx⟩)):=by
  classical
  intro root hu hv A
  obtain ⟨g,hg⟩:=mixed_actual_prescribed_anchor_embedding data π hnoshort σ g₀ g₁ hclasses t Jret w index ext hsupp hsrc
  have hends:=actual_anchor_values_on_run_endpoints data ext hsupp π root g hg
  obtain ⟨f,hf,hglue⟩:=actual_old_matched_embedding_from_endpoint_anchors data hG hCycle b finalExt inner hinner hfinal H u v q hq hlen hqdis
  refine ⟨g,f,hg,hf,?_⟩
  intro hcross
  apply hglue g
  · intro r hp
    exact (hends.1 r hp).trans (hu r).symm
  · intro r hp
    exact (hends.2 r hp).trans (hv r).symm
  · exact hcross
end Oberwolfach
