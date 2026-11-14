module

public import Oberwolfach.PrescribedFamilyRestrictedSaturation
public import Oberwolfach.PrescribedFamilySegmentRestrictedAdvance
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

theorem prescribed_family_segment_restricted_advance_from_state
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
    (H:Finset I) (a κ θ:ℝ) (ha:0<a) (hκ:0<κ) (hθ:0≤θ)
    (hH:(H.card:ℝ)≤a) (hθbudget:θ≤κ*(β/4))
    (hQlocal:∀i∈H,((QV i).card:ℝ)≤θ*Fintype.card V)
    (hLocal:∀v,(((st.freeOccurrences.filter (fun p=>p.1∈H)).filter
      (fun p=>familyVertexImage st.vertexMap p=v)).card:ℝ)≤κ*a+1)
    (hδstrong:δ≤(β/200)^2) (hnstrong:200/β≤(Fintype.card V:ℝ)):
    ∃ st':PrescribedFamilyState I X V,
      st'.Valid QV Q A₀ ψ E₀ J (Real.sqrt δ*Fintype.card V) ∧
      (∀v,(((st'.freeOccurrences.filter (fun p=>p.1∈H)).filter
        (fun p=>familyVertexImage st'.vertexMap p=v)).card:ℝ)≤κ*a+1) ∧
      st'.assigned=Function.update st.assigned k (st.assigned k∪seg.free.toFinset) ∧
      st'.sourceEdges=Function.update st.sourceEdges k
        (st.sourceEdges k∪prescribedOrderedPathEdges (prescribedPathSegmentVertices seg)) ∧
      (∀ i x,x∈st.assigned i→st'.vertexMap i x=st.vertexMap i x) ∧
      (∀ x∈seg.free,st'.vertexMap k x∈L) ∧
      List.IsChain D ((prescribedPathSegmentVertices seg).map (st'.vertexMap k)) :=by
  have hT:∀p∈st.freeOccurrences,p.2∈QV p.1:=by
    intro p hp
    apply hvalid.2.2.1 p.1
    exact (hvalid.2.1 p.1 p.2).mpr (Or.inr hp)
  let T:=st.freeOccurrences.filter (fun p=>p.1∈H)
  let Slocal:=Finset.univ.filter (fun v=>κ*a≤((T.filter (fun p=>familyVertexImage st.vertexMap p=v)).card:ℝ))
  have hsat:=prescribed_family_restricted_saturation st QV H a κ θ β ha hκ hθ hH hθbudget hQlocal hT
  have hs:(Slocal.card:ℝ)≤β*Fintype.card V/4:=hsat.1
  have hS:∀v,κ*a≤((T.filter (fun p=>familyVertexImage st.vertexMap p=v)).card:ℝ)→v∈Slocal:=hsat.2
  exact prescribed_family_segment_restricted_advance st QV Q A₀ ψ E₀ J β δ hβ hβ1 hδ hδbound
    hnβ hn hI hQsize hQdegree hold hJ hvalid k seg hnodup hne hleft hright hdistinct hfree hsubset
    Dsrc Fsrc hDQ hchain D L hext H (κ*a) Slocal hLocal hS hδstrong hnstrong hs
end Oberwolfach
