module

public import Oberwolfach.PrescribedFamilyFreeCycleRestrictedBudgeted
public import Oberwolfach.PrescribedFamilyRestrictedSaturation
public import Oberwolfach.PrescribedFamilyFreeCycleAdvance
public import Oberwolfach.PrescribedFamilyStateInitial
public import Oberwolfach.PrescribedCycleTargetArcs
public import Oberwolfach.PrescribedPathScheduleEdgeForms

@[expose] public section
/-! Complete a source cycle containing no prescribed vertex. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I X V:Type} [Fintype I] [Fintype X] [Fintype V] [DecidableEq I] [DecidableEq X] [DecidableEq V]

theorem prescribed_cycle_free_restricted_advance
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
    (a:X) (xs:List X) (hnodup:(a::xs).Nodup) (hlen:3≤(a::xs).length)
    (hnoA:∀ x∈a::xs,x∉A₀ k)
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
        D (st'.vertexMap k e.1) (st'.vertexMap k e.2)) ∧
      (a::xs).toFinset⊆st'.assigned k ∧
      prescribedOrderedPathEdges ((a::xs)++[a])⊆st'.sourceEdges k := by
  have hT:∀p∈st.freeOccurrences,p.2∈QV p.1:=by
    intro p hp
    apply hvalid.2.2.1 p.1
    exact (hvalid.2.1 p.1 p.2).mpr (Or.inr hp)
  let T:=st.freeOccurrences.filter (fun p=>p.1∈H)
  let Slocal:=Finset.univ.filter (fun v=>κ*aScale≤((T.filter (fun p=>familyVertexImage st.vertexMap p=v)).card:ℝ))
  have hsat:=prescribed_family_restricted_saturation st QV H aScale κ θ β haScale hκ hθ hH hθbudget hQlocal hT
  have hs:(Slocal.card:ℝ)≤β*Fintype.card V/4:=hsat.1
  have hS:∀v,κ*aScale≤((T.filter (fun p=>familyVertexImage st.vertexMap p=v)).card:ℝ)→v∈Slocal:=hsat.2
  have hfree':∀ x∈a::xs,x∉st.assigned k:=by intro x hx;exact hfree x hx (hnoA x hx)
  obtain ⟨g,F,hv,htrack,hpres,hpath,hlist⟩:=prescribed_family_free_cycle_restricted_advance_with_budget st QV Q A₀ ψ E₀ J β δ
    hβ hβ1 hδ hδbound hnβ hn hI hQsize hQdegree hold hJ hvalid k (a::xs) hnodup hlen hfree' hsubset
    Dsrc Fsrc hDQ hsourcecycle D L hext H (κ*aScale) Slocal hLocal hS hδstrong hnstrong hs
  let es:=prescribedCyclePhysicalEdges (a::xs)
  let add:=es.image (Sym2.map g)
  let st':PrescribedFamilyState I X V:=⟨Function.update st.assigned k (st.assigned k∪(a::xs).toFinset),
    Function.update st.vertexMap k g,st.freeOccurrences∪({k}:Finset I).product (a::xs).toFinset,
    Function.update st.sourceEdges k (st.sourceEdges k∪es),
    Function.update st.physicalEdges k (st.physicalEdges k∪add),
    Function.update st.newEdges k (st.newEdges k∪add)⟩
  have horder:prescribedOrderedPathEdges ((a::xs)++[a])=es:=by
    simpa [es,prescribedCyclePhysicalEdges] using prescribed_ordered_two_sided_edges xs a a
  refine ⟨st',hv,?_,rfl,?_,?_,?_,?_,?_,?_,?_⟩
  · convert htrack using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
  · intro i
    by_cases hi:i=k
    · subst i
      intro x hx
      simp [st',hx]
    · simp [st',Function.update_of_ne hi]
  · intro i
    by_cases hi:i=k
    · subst i;simp [st']
    · simp [st',Function.update_of_ne hi]
  · intro i x hx
    by_cases hi:i=k
    · subst i;simpa [st'] using hpres x hx
    · simp [st',Function.update_of_ne hi]
  · intro x hx hnot
    simpa [st'] using hlist x hx
  · intro e he
    have hh:=prescribed_cycle_target_arcs g D F a xs hpath e he
    simpa [st'] using hh
  · simp [st']
  · rw [horder]
    simp [st']
end Oberwolfach
