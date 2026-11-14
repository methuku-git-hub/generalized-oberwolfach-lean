module

public import Oberwolfach.PrescribedCycleOneBoundaryRestrictedAdvance
public import Oberwolfach.PrescribedCycleTwoBoundaryRestrictedAdvance
public import Oberwolfach.PrescribedCycleTwoBoundaryAdvance
public import Oberwolfach.PrescribedCycleOneBoundaryAdvance

@[expose] public section
/-! A cycle rooted at a prescribed vertex has either one or at least two
prescribed vertices. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I X V:Type} [Fintype I] [Fintype X] [Fintype V] [DecidableEq I] [DecidableEq X] [DecidableEq V]

theorem prescribed_cycle_rooted_restricted_advance
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
    (a:X) (xs:List X) (hnodup:(a::xs).Nodup) (hlen:3≤(a::xs).length) (ha:a∈A₀ k)
    (hsourcecycle:DirectedCycleThrough Dsrc Fsrc (a::xs))
    (st:PrescribedFamilyState I X V)
    (hvalid:st.Valid QV Q A₀ ψ E₀ J (Real.sqrt δ*Fintype.card V))
    (hLocal:∀v,(((st.freeOccurrences.filter (fun p=>p.1∈H)).filter
      (fun p=>familyVertexImage st.vertexMap p=v)).card:ℝ)≤κ*aScale+1)
    (hinit:prescribedInducedSourceEdges (Q k) (A₀ k)⊆st.sourceEdges k)
    (hfree:∀ x∈a::xs,x∉A₀ k→x∉st.assigned k) (hsubset:∀ x∈a::xs,x∈QV k):
    ∃ st':PrescribedFamilyState I X V,
      st'.Valid QV Q A₀ ψ E₀ J (Real.sqrt δ*Fintype.card V) ∧
      (∀v,(((st'.freeOccurrences.filter (fun p=>p.1∈H)).filter
        (fun p=>familyVertexImage st'.vertexMap p=v)).card:ℝ)≤κ*aScale+1) ∧
      st'.assigned=Function.update st.assigned k (st.assigned k∪(a::xs).toFinset) ∧
      (∀ i,st.assigned i⊆st'.assigned i) ∧ (∀ i,st.sourceEdges i⊆st'.sourceEdges i) ∧
      (∀ i x,x∈st.assigned i→st'.vertexMap i x=st.vertexMap i x) ∧
      (∀ x∈a::xs,x∉A₀ k→st'.vertexMap k x∈L) ∧
      (∀ e∈prescribedDirectedPathEdges ((a::xs)++[a]),
        (e.1∈A₀ k ∧ e.2∈A₀ k) ∨ D (st'.vertexMap k e.1) (st'.vertexMap k e.2)) ∧
      (a::xs).toFinset⊆st'.assigned k ∧
      prescribedOrderedPathEdges ((a::xs)++[a])⊆st'.sourceEdges k := by
  by_cases hex:∃ b∈xs,b∈A₀ k
  · obtain ⟨b,hbin,hb⟩:=hex
    exact prescribed_cycle_two_boundary_restricted_advance QV Q A₀ ψ E₀ J β δ hβ hβ1 hδ hδbound hnβ hn hI
      hQsize hQdegree hold hJ k Dsrc Fsrc hDQ D L hext H aScale κ θ haScale hκ hθ hH hθbudget hQlocal hδstrong hnstrong a b xs hnodup ha hb hbin hsourcecycle st hvalid hLocal hinit hfree hsubset
  · have hnoA:∀ x∈xs,x∉A₀ k:=by
      intro x hx hxa;exact hex ⟨x,hx,hxa⟩
    have hlen':2≤xs.length:=by simp only [List.length_cons] at hlen;omega
    obtain ⟨st',hv,hvLocal,haexact,hamono,hemono,hpres,hL,harcs,hvertices,hedges⟩:=
      prescribed_cycle_one_boundary_restricted_advance QV Q A₀ ψ E₀ J β δ hβ hβ1 hδ hδbound hnβ hn hI
        hQsize hQdegree hold hJ k Dsrc Fsrc hDQ D L hext H aScale κ θ haScale hκ hθ hH hθbudget hQlocal hδstrong hnstrong a xs hnodup hlen' ha hnoA hsourcecycle st hvalid hLocal hinit hfree hsubset
    refine ⟨st',hv,hvLocal,haexact,hamono,hemono,hpres,hL,?_,hvertices,hedges⟩
    intro e he;exact Or.inr (harcs e he)
end Oberwolfach
