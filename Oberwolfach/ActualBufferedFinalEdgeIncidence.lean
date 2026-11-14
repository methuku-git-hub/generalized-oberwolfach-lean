module

public import Oberwolfach.ActualSumBufferedInteriorsDeleted
public import Oberwolfach.ResidualInternalNeighbors
public import Oberwolfach.ResidualDeletedPathProperties
public import Oberwolfach.ActualRestrictedEdgeCover

@[expose] public section
/-! In a two-factor, every edge at a final buffered-path interior is one of
the final path edges.  Thus old nonfinal edges avoid these interiors. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_buffered_final_edge_incidence
    {X A B J:Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [DecidableEq B] [DecidableEq J]
    {F:SimpleGraph X} (data:ActualResidualData (K:=A⊕B) (J:=J) F) (hF:F.IsRegularOfDegree 2)
    (hs:data.s₁=firstSumIndices)
    (ext:∀i:A⊕B,Fin (data.c*data.d+5)↪X)
    (inner:∀a:A,Fin (data.c*data.d+1)↪X)
    (hsupp:∀i,(data.P i).support=List.ofFn (ext i))
    (hinner:∀a k,inner a k=ext (.inl a) ⟨k.val+2,by omega⟩):
    let Interiors:=bufferedPathStrictInterior (fun _:A=>data.c*data.d) inner
    let Final:=Finset.univ.biUnion (fun i:{i // i∈data.s₁}=>(data.path (.inl i)).edges.toFinset)
    (∀x∈Interiors,∀y,F.Adj x y→s(x,y)∈Final) ∧ Final⊆data.deletedEdges ∧
    (∀e∈data.deletedEdges\Final,∀x∈e.toFinset,x∉Interiors):=by
  intro Interiors Final
  let ix (a:A):{i // i∈data.s₁}:=⟨.inl a,by rw [hs];simp [firstSumIndices]⟩
  have hpaths:=deleted_path_family_properties F data.s₁ data.s₂ data.u data.v data.P data.hp data.c data.d
    (by have hh:=data.hc; omega) data.hd data.hlen data.T (fun i _=>data.hT i)
  have hIncident:∀x∈Interiors,∀y,F.Adj x y→s(x,y)∈Final:=by
    intro x hx y hxy
    obtain ⟨i,_,hx⟩:=Finset.mem_biUnion.mp hx
    obtain ⟨p,hp,rfl⟩:=Finset.mem_image.mp hx
    have hp0:0<p.val:=(Finset.mem_filter.mp hp).2.1
    have hpn:p.val<data.c*data.d:=(Finset.mem_filter.mp hp).2.2
    have hpath:=actual_final_path_matches_buffered_sequence data (ix i) (ext (.inl i)) (inner i) (hinner i) (hsupp (.inl i))
    have hsupp':inner i p∈(data.path (.inl (ix i))).support.toFinset:=by
      rw [hpath.2.2]
      exact List.mem_toFinset.mpr (List.mem_ofFn.mpr ⟨p,rfl⟩)
    have hn0:inner i p≠data.start (.inl (ix i)):=by
      rw [hpath.1]
      intro he
      have hh:p=0:=(inner i).injective he
      have hv:p.val=0:=by simpa only [Fin.val_zero] using congrArg Fin.val hh
      omega
    have hn1:inner i p≠data.finish (.inl (ix i)):=by
      rw [hpath.2.1]
      intro he
      have hh:p=Fin.last (data.c*data.d):=(inner i).injective he
      have hv:=congrArg Fin.val hh
      simp at hv
      omega
    have hInt:inner i p∈(data.path (.inl (ix i))).support.toFinset\
        {data.start (.inl (ix i)),data.finish (.inl (ix i))}:=by
      exact Finset.mem_sdiff.mpr ⟨hsupp',by simp [hn0,hn1]⟩
    have he:=two_factor_internal_path_edges F hF (data.path (.inl (ix i))) (hpaths (.inl (ix i))).1 (inner i p) y hInt hxy
    exact Finset.mem_biUnion.mpr ⟨ix i,Finset.mem_univ _,he⟩
  refine ⟨hIncident,?_,?_⟩
  · intro e he
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp he
    change e∈data.t.biUnion (fun j=>(data.C j).edges.toFinset) ∪
      Finset.univ.biUnion (fun z:data.Z=>(data.path z).edges.toFinset)
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨.inl i,Finset.mem_univ _,hi⟩)
  · intro e he x hx hI
    have heF:data.deletedEdges⊆F.edgeFinset:=data.deleted_edges_subset_factor
    have hadj:e∈F.edgeFinset:=heF (Finset.mem_sdiff.mp he).1
    induction e using Sym2.ind with
    | _ u v =>
      have huv:F.Adj u v:=SimpleGraph.mem_edgeFinset.mp hadj
      have hx':x=u∨x=v:=by simpa using hx
      rcases hx' with hxu|hxv
      · subst x
        exact (Finset.mem_sdiff.mp he).2 (hIncident u hI v huv)
      · subst x
        apply (Finset.mem_sdiff.mp he).2
        simpa only [Sym2.eq_swap] using hIncident v hI u huv.symm
end Oberwolfach
