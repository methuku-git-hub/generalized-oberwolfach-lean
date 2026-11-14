module

public import Oberwolfach.PrescribedFamilyOneEndedRestrictedBudgeted
public import Oberwolfach.PrescribedFamilyTwoEndedRestrictedBudgeted
public import Oberwolfach.PrescribedFamilyFreePathRestrictedBudgeted
public import Oberwolfach.PrescribedFamilyOneEndedAdvance
public import Oberwolfach.PrescribedFamilyTwoEndedAdvance
public import Oberwolfach.PrescribedFamilyFreePathAdvance
public import Oberwolfach.PrescribedPathScheduleChain
public import Oberwolfach.PrescribedPathScheduleEdgeForms
public import Oberwolfach.PrescribedTargetPathChains

@[expose] public section
/-! Embed a nonempty scheduled source-path segment and add exactly its edges
while preserving the family state. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I X V:Type} [Fintype I] [Fintype X] [Fintype V] [DecidableEq I] [DecidableEq X] [DecidableEq V]

theorem prescribed_family_segment_restricted_advance
    (st:PrescribedFamilyState I X V) (QV:I→Finset X) (Q:I→SimpleGraph X)
    (A₀:I→Finset X) (ψ:I→X→V) (E₀:I→Finset (Sym2 V)) (J:SimpleGraph V)
    (β δ:ℝ) (hβ:0<β) (hβ1:β≤1) (hδ:0<δ) (hδbound:δ≤(β/100)^2)
    (hnβ:100/β≤(Fintype.card V:ℝ)) (hn:2/Real.sqrt δ≤(Fintype.card V:ℝ))
    (hI:(Fintype.card I:ℝ)≤Fintype.card V)
    (hQsize:∀ i,((QV i).card:ℝ)≤δ*Fintype.card V) (hQdegree:∀ i x,(Q i).degree x≤2)
    (hold:∀ v,((Finset.univ.filter (fun i=>∃ x,x∈A₀ i ∧ ψ i x=v)).card:ℝ)≤δ*Fintype.card V)
    (hJ:∀ v,(J.degree v:ℝ)≤δ*Fintype.card V)
    (hvalid:st.Valid QV Q A₀ ψ E₀ J (Real.sqrt δ*Fintype.card V))
    (k:I) (seg:PrescribedPathSegment X) (hnodup:seg.free.Nodup) (hne:seg.free≠[])
    (hleft:∀ a,seg.left=some a→a∈st.assigned k)
    (hright:∀ b,seg.right=some b→b∈st.assigned k)
    (hdistinct:∀ a b,seg.left=some a→seg.right=some b→a≠b)
    (hfree:∀ x∈seg.free,x∉st.assigned k) (hsubset:∀ x∈seg.free,x∈QV k)
    (Dsrc:X→X→Prop) (Fsrc:SimpleGraph X) (hDQ:∀ x y,Dsrc x y→(Q k).Adj x y)
    (hchain:List.IsChain (fun x y=>Dsrc x y ∧ ¬Fsrc.Adj x y) (prescribedPathSegmentVertices seg))
    (D:V→V→Prop) (L:Finset V) (hext:IsExtendingList D L β)
    (H:Finset I) (tLocal:ℝ) (Slocal:Finset V)
    (hLocal:∀v,(((st.freeOccurrences.filter (fun p=>p.1∈H)).filter
      (fun p=>familyVertexImage st.vertexMap p=v)).card:ℝ)≤tLocal+1)
    (hSat:∀v,tLocal≤(((st.freeOccurrences.filter (fun p=>p.1∈H)).filter
      (fun p=>familyVertexImage st.vertexMap p=v)).card:ℝ)→v∈Slocal)
    (hδstrong:δ≤(β/200)^2) (hnstrong:200/β≤(Fintype.card V:ℝ))
    (hExtra:(Slocal.card:ℝ)≤β*Fintype.card V/4):
    ∃ st':PrescribedFamilyState I X V,
      st'.Valid QV Q A₀ ψ E₀ J (Real.sqrt δ*Fintype.card V) ∧
      (∀v,(((st'.freeOccurrences.filter (fun p=>p.1∈H)).filter
        (fun p=>familyVertexImage st'.vertexMap p=v)).card:ℝ)≤tLocal+1) ∧
      st'.assigned=Function.update st.assigned k (st.assigned k∪seg.free.toFinset) ∧
      st'.sourceEdges=Function.update st.sourceEdges k
        (st.sourceEdges k∪prescribedOrderedPathEdges (prescribedPathSegmentVertices seg)) ∧
      (∀ i x,x∈st.assigned i→st'.vertexMap i x=st.vertexMap i x) ∧
      (∀ x∈seg.free,st'.vertexMap k x∈L) ∧
      List.IsChain D ((prescribedPathSegmentVertices seg).map (st'.vertexMap k)) := by
  rcases seg with ⟨left,as,right⟩
  cases left with
  | none =>
    cases right with
    | none =>
      have hlen:1≤as.length:=by cases as with | nil => contradiction | cons => simp
      have hs:=prescribed_path_segment_free_path Dsrc Fsrc ⟨none,as,none⟩ rfl rfl hne hchain
      obtain ⟨g,F,hv,htrack,hpres,hpath,hlist⟩:=prescribed_family_free_path_restricted_advance_with_budget st QV Q A₀ ψ E₀ J β δ hβ hβ1 hδ hδbound
        hnβ hn hI hQsize hQdegree hold hJ hvalid k as hnodup hlen hfree hsubset Dsrc Fsrc hDQ hs D L hext H tLocal Slocal hLocal hSat hδstrong hnstrong hExtra
      let es:=prescribedFreePathPhysicalEdges as
      let add:=es.image (Sym2.map g)
      let st':PrescribedFamilyState I X V:=⟨Function.update st.assigned k (st.assigned k∪as.toFinset),
        Function.update st.vertexMap k g,st.freeOccurrences∪({k}:Finset I).product as.toFinset,
        Function.update st.sourceEdges k (st.sourceEdges k∪es),
        Function.update st.physicalEdges k (st.physicalEdges k∪add),
        Function.update st.newEdges k (st.newEdges k∪add)⟩
      refine ⟨st',hv,?_,rfl,?_,?_,?_,?_⟩
      · convert htrack using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
      · simp [st',es,prescribedPathSegmentVertices,prescribed_ordered_free_path_edges]
      · intro i x hx
        by_cases hi:i=k
        · subst i;simpa [st'] using hpres x hx
        · simp [st',Function.update_of_ne hi]
      · intro x hx
        simpa [st'] using hlist x hx
      · simpa [st',prescribedPathSegmentVertices,List.cons_append] using (prescribed_target_free_chain g D F as hpath)

    | some b =>
      have hs:=prescribed_path_segment_right_path Dsrc Fsrc ⟨none,as,some b⟩ b rfl rfl hchain
      have hrevfree:∀ x∈as.reverse,x∉st.assigned k:=by simpa using hfree
      have hrevsub:∀ x∈as.reverse,x∈QV k:=by simpa using hsubset
      have hrevnodup:as.reverse.Nodup:=by simpa using (List.nodup_reverse.mpr hnodup)
      obtain ⟨g,F,hv,htrack,hpres,hpath,hlist⟩:=prescribed_family_one_ended_restricted_advance_with_budget st QV Q A₀ ψ E₀ J β δ hβ hβ1 hδ hδbound
        hnβ hn hI hQsize hQdegree hold hJ hvalid k b as.reverse hrevnodup (hright b rfl)
        hrevfree hrevsub Dsrc Fsrc false hDQ hs D L hext H tLocal Slocal hLocal hSat hδstrong hnstrong hExtra
      let es:=prescribedOneSidedPhysicalEdges b as.reverse
      let add:=es.image (Sym2.map g)
      let st':PrescribedFamilyState I X V:=⟨Function.update st.assigned k (st.assigned k∪as.reverse.toFinset),
        Function.update st.vertexMap k g,st.freeOccurrences∪({k}:Finset I).product as.reverse.toFinset,
        Function.update st.sourceEdges k (st.sourceEdges k∪es),
        Function.update st.physicalEdges k (st.physicalEdges k∪add),
        Function.update st.newEdges k (st.newEdges k∪add)⟩
      refine ⟨st',hv,?_,?_,?_,?_,?_,?_⟩
      · convert htrack using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
      · simp [st']
      · simp [st',es,prescribedPathSegmentVertices,prescribed_ordered_right_sided_edges]
      · intro i x hx
        by_cases hi:i=k
        · subst i;simpa [st'] using hpres x hx
        · simp [st',Function.update_of_ne hi]
      · intro x hx
        simpa [st'] using hlist x (by simpa using hx)
      · simpa [st',prescribedPathSegmentVertices] using (prescribed_target_right_chain g D F b as hpath)

  | some a =>
    cases right with
    | none =>
      have hs:=prescribed_path_segment_left_path Dsrc Fsrc ⟨some a,as,none⟩ a rfl rfl hchain
      obtain ⟨g,F,hv,htrack,hpres,hpath,hlist⟩:=prescribed_family_one_ended_restricted_advance_with_budget st QV Q A₀ ψ E₀ J β δ hβ hβ1 hδ hδbound
        hnβ hn hI hQsize hQdegree hold hJ hvalid k a as hnodup (hleft a rfl) hfree hsubset Dsrc Fsrc true hDQ hs D L hext H tLocal Slocal hLocal hSat hδstrong hnstrong hExtra
      let es:=prescribedOneSidedPhysicalEdges a as
      let add:=es.image (Sym2.map g)
      let st':PrescribedFamilyState I X V:=⟨Function.update st.assigned k (st.assigned k∪as.toFinset),
        Function.update st.vertexMap k g,st.freeOccurrences∪({k}:Finset I).product as.toFinset,
        Function.update st.sourceEdges k (st.sourceEdges k∪es),
        Function.update st.physicalEdges k (st.physicalEdges k∪add),
        Function.update st.newEdges k (st.newEdges k∪add)⟩
      refine ⟨st',hv,?_,rfl,?_,?_,?_,?_⟩
      · convert htrack using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
      · simp [st',es,prescribedPathSegmentVertices,prescribed_ordered_one_sided_edges]
      · intro i x hx
        by_cases hi:i=k
        · subst i;simpa [st'] using hpres x hx
        · simp [st',Function.update_of_ne hi]
      · intro x hx
        simpa [st'] using hlist x hx
      · simpa [st',prescribedPathSegmentVertices,List.cons_append] using (prescribed_target_left_chain g D F a as hpath)

    | some b =>
      have hlen:1≤as.length:=by cases as with | nil => contradiction | cons => simp
      have hs:=prescribed_path_segment_two_path Dsrc Fsrc ⟨some a,as,some b⟩ a b rfl rfl hchain
      obtain ⟨g,F,hv,htrack,hpres,hpath,hlist⟩:=prescribed_family_two_ended_restricted_advance_with_budget st QV Q A₀ ψ E₀ J β δ hβ hβ1 hδ hδbound
        hnβ hn hI hQsize hQdegree hold hJ hvalid k a b as hnodup hlen (hleft a rfl) (hright b rfl)
        (hdistinct a b rfl rfl) hfree hsubset Dsrc Fsrc hDQ hs D L hext H tLocal Slocal hLocal hSat hδstrong hnstrong hExtra
      let es:=prescribedPathPhysicalEdges a b as
      let add:=es.image (Sym2.map g)
      let st':PrescribedFamilyState I X V:=⟨Function.update st.assigned k (st.assigned k∪as.toFinset),
        Function.update st.vertexMap k g,st.freeOccurrences∪({k}:Finset I).product as.toFinset,
        Function.update st.sourceEdges k (st.sourceEdges k∪es),
        Function.update st.physicalEdges k (st.physicalEdges k∪add),
        Function.update st.newEdges k (st.newEdges k∪add)⟩
      refine ⟨st',hv,?_,rfl,?_,?_,?_,?_⟩
      · convert htrack using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
      · have he:=prescribed_ordered_two_sided_edges as a b
        simp only [List.cons_append] at he
        simpa [st',es,prescribedPathSegmentVertices,he]
      · intro i x hx
        by_cases hi:i=k
        · subst i;simpa [st'] using hpres x hx
        · simp [st',Function.update_of_ne hi]
      · intro x hx
        simpa [st'] using hlist x hx
      · simpa [st',prescribedPathSegmentVertices,List.cons_append] using (prescribed_target_two_chain g D F a b as hpath)

end Oberwolfach
