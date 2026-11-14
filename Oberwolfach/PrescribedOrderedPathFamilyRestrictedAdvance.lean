module

public import Oberwolfach.PrescribedSegmentScheduleRestrictedInduction
public import Oberwolfach.PrescribedSegmentScheduleInduction
public import Oberwolfach.PrescribedScheduledPathArcs

@[expose] public section
/-! Apply the finite schedule induction to an actual ordered source path. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I X V:Type} [Fintype I] [Fintype X] [Fintype V] [DecidableEq I] [DecidableEq X] [DecidableEq V]

theorem prescribed_ordered_path_family_restricted_advance
    (QV:I→Finset X) (Q:I→SimpleGraph X) (A₀:I→Finset X) (ψ:I→X→V)
    (E₀:I→Finset (Sym2 V)) (J:SimpleGraph V)
    (β δ:ℝ) (hβ:0<β) (hβ1:β≤1) (hδ:0<δ) (hδbound:δ≤(β/100)^2)
    (hnβ:100/β≤(Fintype.card V:ℝ)) (hn:2/Real.sqrt δ≤(Fintype.card V:ℝ))
    (hI:(Fintype.card I:ℝ)≤Fintype.card V)
    (hQsize:∀ i,((QV i).card:ℝ)≤δ*Fintype.card V) (hQdegree:∀ i x,(Q i).degree x≤2)
    (hold:∀ v,((Finset.univ.filter (fun i=>∃ x,x∈A₀ i ∧ ψ i x=v)).card:ℝ)≤δ*Fintype.card V)
    (hJ:∀ v,(J.degree v:ℝ)≤δ*Fintype.card V)
    (k:I) (Dsrc:X→X→Prop) (Fsrc:SimpleGraph X) (hDQ:∀ x y,Dsrc x y→(Q k).Adj x y)
    (D:V→V→Prop) (L:Finset V) (hext:IsExtendingList D L β)
    (H:Finset I) (aScale κ θ:ℝ) (haScale:0<aScale) (hκ:0<κ) (hθ:0≤θ)
    (hH:(H.card:ℝ)≤aScale) (hθbudget:θ≤κ*(β/4))
    (hQlocal:∀i∈H,((QV i).card:ℝ)≤θ*Fintype.card V)
    (hδstrong:δ≤(β/200)^2) (hnstrong:200/β≤(Fintype.card V:ℝ))
    (xs:List X) (hxs:xs.Nodup)
    (hsourcechain:List.IsChain (fun x y=>Dsrc x y ∧ ¬Fsrc.Adj x y) xs)
    (st:PrescribedFamilyState I X V)
    (hvalid:st.Valid QV Q A₀ ψ E₀ J (Real.sqrt δ*Fintype.card V))
    (hLocal:∀v,(((st.freeOccurrences.filter (fun p=>p.1∈H)).filter
      (fun p=>familyVertexImage st.vertexMap p=v)).card:ℝ)≤κ*aScale+1)
    (hinit:prescribedInducedSourceEdges (Q k) (A₀ k)⊆st.sourceEdges k)
    (hfree:∀ x∈xs,x∉A₀ k→x∉st.assigned k) (hsubset:∀ x∈xs,x∈QV k):
    ∃ st':PrescribedFamilyState I X V,
      st'.Valid QV Q A₀ ψ E₀ J (Real.sqrt δ*Fintype.card V) ∧
      (∀v,(((st'.freeOccurrences.filter (fun p=>p.1∈H)).filter
        (fun p=>familyVertexImage st'.vertexMap p=v)).card:ℝ)≤κ*aScale+1) ∧
      st'.assigned=Function.update st.assigned k (st.assigned k∪xs.toFinset) ∧
      (∀ i,st.assigned i⊆st'.assigned i) ∧ (∀ i,st.sourceEdges i⊆st'.sourceEdges i) ∧
      (∀ i x,x∈st.assigned i→st'.vertexMap i x=st.vertexMap i x) ∧
      (∀ x∈xs,x∉A₀ k→st'.vertexMap k x∈L) ∧
      (∀ seg∈prescribedPathSegments (A₀ k) none [] xs,seg.free≠[]→
        List.IsChain D ((prescribedPathSegmentVertices seg).map (st'.vertexMap k))) ∧
      (∀ e∈prescribedDirectedPathEdges xs,(e.1∈A₀ k ∧ e.2∈A₀ k) ∨
        D (st'.vertexMap k e.1) (st'.vertexMap k e.2)) ∧
      xs.toFinset⊆st'.assigned k ∧ prescribedOrderedPathEdges xs⊆st'.sourceEdges k := by
  let segs:=prescribedPathSegments (A₀ k) none [] xs
  have hcompat:PrescribedSegmentsCompatible (A₀ k) Dsrc Fsrc segs:=by
    intro seg hseg
    have hb:=prescribed_path_segment_boundaries (A₀ k) xs none [] (by simp) seg hseg
    have hd:=prescribed_path_segment_boundaries_distinct (A₀ k) xs none [] hxs (by simp) seg hseg
    exact ⟨hb.1,hb.2,hd,prescribed_path_segment_inherits_chain (A₀ k) xs _ hsourcechain seg hseg⟩
  have heq:segs.flatMap PrescribedPathSegment.free=xs.filter (fun x=>x∉A₀ k):=by
    simpa [segs] using prescribed_path_segments_free_vertices (A₀ k) xs none []
  have hnodup:(segs.flatMap PrescribedPathSegment.free).Nodup:=by
    rw [heq];exact hxs.filter _
  have hf:∀ x∈segs.flatMap PrescribedPathSegment.free,x∉st.assigned k:=by
    intro x hx
    rw [heq] at hx
    exact hfree x (List.mem_filter.mp hx).1 (by simpa using (List.mem_filter.mp hx).2)
  have hs:∀ x∈segs.flatMap PrescribedPathSegment.free,x∈QV k:=by
    intro x hx
    rw [heq] at hx
    exact hsubset x (List.mem_filter.mp hx).1
  obtain ⟨st',hv,hvLocal,haexact,ha,he,hpres,hL,hchains,hvertices,hedges⟩:=prescribed_segment_schedule_restricted_induction QV Q A₀ ψ E₀ J
    β δ hβ hβ1 hδ hδbound hnβ hn hI hQsize hQdegree hold hJ k Dsrc Fsrc hDQ D L hext
    H aScale κ θ haScale hκ hθ hH hθbudget hQlocal hδstrong hnstrong segs st hvalid hLocal hinit hcompat hnodup hf hs
  refine ⟨st',hv,hvLocal,?_,ha,he,hpres,?_,?_,?_,?_,?_⟩
  · have hu:st.assigned k ∪ (xs.filter (fun x=>x∉A₀ k)).toFinset = st.assigned k ∪ xs.toFinset:=by
      ext x
      by_cases hx:x∈st.assigned k
      · simp [hx]
      · have hnot:x∉A₀ k:=by intro h;exact hx ((hvalid.2.1 k x).mpr (Or.inl h))
        simp [hx,hnot]
    rw [haexact,heq,hu]
  · intro x hx hnot
    apply hL x
    rw [heq]
    exact List.mem_filter.mpr ⟨hx,by simpa using hnot⟩
  · exact hchains
  · exact prescribed_scheduled_path_arcs (A₀ k) xs (st'.vertexMap k) D hchains
  · intro x hx
    by_cases hxA:x∈A₀ k
    · exact ha k ((hvalid.2.1 k x).mpr (Or.inl hxA))
    · apply hvertices
      apply List.mem_toFinset.mpr
      rw [heq]
      exact List.mem_filter.mpr ⟨List.mem_toFinset.mp hx,by simpa using hxA⟩
  · have he':prescribedSegmentEdges segs=prescribedOrderedPathEdges xs:=by
      simpa [segs] using prescribed_path_segments_edge_union (A₀ k) xs none []
    rw [←he'];exact hedges
end Oberwolfach
