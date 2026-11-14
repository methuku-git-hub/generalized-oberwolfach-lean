module

public import Oberwolfach.PrescribedFamilySegmentAdvance
public import Oberwolfach.PrescribedEmptySegmentEdges

@[expose] public section
/-! Iterate ordered source-path segments while preserving assigned images,
free-image lists and the exact source-edge accounting. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I X V:Type} [Fintype I] [Fintype X] [Fintype V] [DecidableEq I] [DecidableEq X] [DecidableEq V]

def PrescribedSegmentsCompatible (A:Finset X) (D:X→X→Prop) (F:SimpleGraph X)
    (segs:List (PrescribedPathSegment X)):Prop:=
  ∀ seg∈segs,
    (∀ a,seg.left=some a→a∈A) ∧ (∀ b,seg.right=some b→b∈A) ∧
    (∀ a b,seg.left=some a→seg.right=some b→a≠b) ∧
    List.IsChain (fun x y=>D x y ∧ ¬F.Adj x y) (prescribedPathSegmentVertices seg)

theorem prescribed_segment_schedule_induction
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
    (segs:List (PrescribedPathSegment X)) (st:PrescribedFamilyState I X V)
    (hvalid:st.Valid QV Q A₀ ψ E₀ J (Real.sqrt δ*Fintype.card V))
    (hinit:prescribedInducedSourceEdges (Q k) (A₀ k)⊆st.sourceEdges k)
    (hcompat:PrescribedSegmentsCompatible (A₀ k) Dsrc Fsrc segs)
    (hnodup:(segs.flatMap PrescribedPathSegment.free).Nodup)
    (hfree:∀ x∈segs.flatMap PrescribedPathSegment.free,x∉st.assigned k)
    (hsubset:∀ x∈segs.flatMap PrescribedPathSegment.free,x∈QV k):
    ∃ st':PrescribedFamilyState I X V,
      st'.Valid QV Q A₀ ψ E₀ J (Real.sqrt δ*Fintype.card V) ∧
      st'.assigned=Function.update st.assigned k
        (st.assigned k∪(segs.flatMap PrescribedPathSegment.free).toFinset) ∧
      (∀ i,st.assigned i⊆st'.assigned i) ∧ (∀ i,st.sourceEdges i⊆st'.sourceEdges i) ∧
      (∀ i x,x∈st.assigned i→st'.vertexMap i x=st.vertexMap i x) ∧
      (∀ x∈segs.flatMap PrescribedPathSegment.free,st'.vertexMap k x∈L) ∧
      (∀ seg∈segs,seg.free≠[]→List.IsChain D ((prescribedPathSegmentVertices seg).map (st'.vertexMap k))) ∧
      (segs.flatMap PrescribedPathSegment.free).toFinset⊆st'.assigned k ∧
      prescribedSegmentEdges segs⊆st'.sourceEdges k := by
  induction segs generalizing st with
  | nil =>
    refine ⟨st,hvalid,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · funext i
      by_cases hi:i=k
      · subst i;simp
      · simp [Function.update_of_ne hi]
    · intro i;exact Finset.Subset.rfl
    · intro i;exact Finset.Subset.rfl
    · intro i x hx;rfl
    · simp
    · simp
    · simp
    · simp [prescribedSegmentEdges]
  | cons seg rest ih =>
    have hc:=hcompat seg (by simp)
    have hcrest:PrescribedSegmentsCompatible (A₀ k) Dsrc Fsrc rest:=by
      intro q hq;exact hcompat q (by simp [hq])
    simp only [List.flatMap_cons] at hnodup hfree hsubset
    have hnparts:=List.nodup_append'.mp hnodup
    have hleft:∀ a,seg.left=some a→a∈st.assigned k:=by
      intro a ha;exact (hvalid.2.1 k a).mpr (Or.inl (hc.1 a ha))
    have hright:∀ b,seg.right=some b→b∈st.assigned k:=by
      intro b hb;exact (hvalid.2.1 k b).mpr (Or.inl (hc.2.1 b hb))
    by_cases hempty:seg.free=[]
    · have hemptyE:prescribedOrderedPathEdges (prescribedPathSegmentVertices seg)⊆st.sourceEdges k:=
        (prescribed_empty_segment_edges (Q k) Fsrc (A₀ k) Dsrc hDQ seg hempty hc.1 hc.2.1 hc.2.2.2).trans hinit
      have hfreerest:∀ x∈rest.flatMap PrescribedPathSegment.free,x∉st.assigned k:=by
        intro x hx;exact hfree x (List.mem_append_right _ hx)
      have hsubrest:∀ x∈rest.flatMap PrescribedPathSegment.free,x∈QV k:=by
        intro x hx;exact hsubset x (List.mem_append_right _ hx)
      obtain ⟨st',hv,haexact,ha,he,hpres,hL,hchains,hvertices,hedges⟩:=ih st hvalid hinit hcrest hnparts.2.1 hfreerest hsubrest
      refine ⟨st',hv,?_,ha,he,hpres,?_,?_,?_,?_⟩
      · simpa [hempty] using haexact
      · simpa [hempty] using hL
      · intro q hq hne
        rcases List.mem_cons.mp hq with hq|hq
        · subst q;exact (hne hempty).elim
        · exact hchains q hq hne
      · simpa [hempty] using hvertices
      · simp only [prescribedSegmentEdges,List.toFinset_cons,Finset.biUnion_insert]
        exact Finset.union_subset (hemptyE.trans (he k)) hedges
    · have hheadfree:∀ x∈seg.free,x∉st.assigned k:=by
        intro x hx;exact hfree x (List.mem_append_left _ hx)
      have hheadsub:∀ x∈seg.free,x∈QV k:=by
        intro x hx;exact hsubset x (List.mem_append_left _ hx)
      obtain ⟨mid,hm,hmA,hmE,hmpres,hmL,hmchain⟩:=prescribed_family_segment_advance st QV Q A₀ ψ E₀ J β δ
        hβ hβ1 hδ hδbound hnβ hn hI hQsize hQdegree hold hJ hvalid k seg hnparts.1 hempty hleft hright
        hc.2.2.1 hheadfree hheadsub Dsrc Fsrc hDQ hc.2.2.2 D L hext
      have hamono:∀ i,st.assigned i⊆mid.assigned i:=by
        intro i
        rw [hmA]
        by_cases hi:i=k
        · subst i;simp
        · simp [Function.update_of_ne hi]
      have hemono:∀ i,st.sourceEdges i⊆mid.sourceEdges i:=by
        intro i
        rw [hmE]
        by_cases hi:i=k
        · subst i;simp
        · simp [Function.update_of_ne hi]
      have hinitmid:prescribedInducedSourceEdges (Q k) (A₀ k)⊆mid.sourceEdges k:=hinit.trans (hemono k)
      have hfreerest:∀ x∈rest.flatMap PrescribedPathSegment.free,x∉mid.assigned k:=by
        intro x hx hxmid
        rw [hmA,Function.update_self] at hxmid
        rcases Finset.mem_union.mp hxmid with hxold|hxhead
        · exact hfree x (List.mem_append_right _ hx) hxold
        · exact (List.disjoint_left.mp hnparts.2.2 (List.mem_toFinset.mp hxhead)) hx
      have hsubrest:∀ x∈rest.flatMap PrescribedPathSegment.free,x∈QV k:=by
        intro x hx;exact hsubset x (List.mem_append_right _ hx)
      obtain ⟨last,hl,haexact,ha,he,hpres,hL,hchains,hvertices,hedges⟩:=ih mid hm hinitmid hcrest hnparts.2.1 hfreerest hsubrest
      refine ⟨last,hl,?_,?_,?_,?_,?_,?_,?_,?_⟩
      · rw [haexact,hmA]
        funext i
        by_cases hi:i=k
        · subst i;simp [List.flatMap_cons,List.toFinset_append,Finset.union_assoc]
        · simp [Function.update_of_ne hi]
      · intro i;exact (hamono i).trans (ha i)
      · intro i;exact (hemono i).trans (he i)
      · intro i x hx;exact (hpres i x (hamono i hx)).trans (hmpres i x hx)
      · intro x hx
        simp only [List.flatMap_cons,List.mem_append] at hx
        rcases hx with hx|hx
        · have hxmid:x∈mid.assigned k:=by rw [hmA,Function.update_self];exact Finset.mem_union_right _ (List.mem_toFinset.mpr hx)
          rw [hpres k x hxmid];exact hmL x hx
        · exact hL x hx
      · intro q hq hne
        rcases List.mem_cons.mp hq with hq|hq
        · subst q
          have hmember:∀ x∈prescribedPathSegmentVertices seg,x∈mid.assigned k:=by
            intro x hx
            simp only [prescribedPathSegmentVertices,List.mem_append,Option.mem_toList] at hx
            rcases hx with (hx|hx)|hx
            · exact hamono k (hleft x hx)
            · rw [hmA,Function.update_self];exact Finset.mem_union_right _ (List.mem_toFinset.mpr hx)
            · exact hamono k (hright x hx)
          have hmap:(prescribedPathSegmentVertices seg).map (last.vertexMap k) =
              (prescribedPathSegmentVertices seg).map (mid.vertexMap k):=by
            apply List.map_congr_left
            intro x hx;exact hpres k x (hmember x hx)
          rw [hmap];exact hmchain
        · exact hchains q hq hne
      · intro x hx
        simp only [List.toFinset_cons,List.flatMap_cons,List.toFinset_append,Finset.mem_union] at hx
        rcases hx with hx|hx
        · exact ha k (by rw [hmA,Function.update_self];exact Finset.mem_union_right _ hx)
        · exact hvertices hx
      · simp only [prescribedSegmentEdges,List.toFinset_cons,Finset.biUnion_insert]
        apply Finset.union_subset
        · have hh:prescribedOrderedPathEdges (prescribedPathSegmentVertices seg)⊆mid.sourceEdges k:=by
            rw [hmE,Function.update_self]
            exact Finset.subset_union_right
          exact hh.trans (he k)
        · exact hedges
end Oberwolfach
