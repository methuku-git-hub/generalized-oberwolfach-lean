module

public import Oberwolfach.PrescribedSourcePieces
public import Oberwolfach.PrescribedOrderedPathFamilyRestrictedAdvance
public import Oberwolfach.PrescribedCycleFamilyRestrictedAdvance

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X:Type} [DecidableEq X]
variable {I V:Type} [Fintype I] [Fintype X] [Fintype V] [DecidableEq I] [DecidableEq V]

theorem prescribed_source_piece_restricted_advance
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
    (p:PrescribedSourcePiece X) (hp:p.Valid Dsrc Fsrc) (st:PrescribedFamilyState I X V)
    (hvalid:st.Valid QV Q A₀ ψ E₀ J (Real.sqrt δ*Fintype.card V))
    (hLocal:∀v,(((st.freeOccurrences.filter (fun p=>p.1∈H)).filter
      (fun p=>familyVertexImage st.vertexMap p=v)).card:ℝ)≤κ*aScale+1)
    (hinit:prescribedInducedSourceEdges (Q k) (A₀ k)⊆st.sourceEdges k)
    (hfree:∀ x∈p.vertices,x∉A₀ k→x∉st.assigned k) (hsubset:∀ x∈p.vertices,x∈QV k):
    ∃ st':PrescribedFamilyState I X V,
      st'.Valid QV Q A₀ ψ E₀ J (Real.sqrt δ*Fintype.card V) ∧
      (∀v,(((st'.freeOccurrences.filter (fun p=>p.1∈H)).filter
        (fun p=>familyVertexImage st'.vertexMap p=v)).card:ℝ)≤κ*aScale+1) ∧
      st'.assigned=Function.update st.assigned k (st.assigned k∪p.vertices.toFinset) ∧
      (∀ i,st.assigned i⊆st'.assigned i) ∧ (∀ i,st.sourceEdges i⊆st'.sourceEdges i) ∧
      (∀ i x,x∈st.assigned i→st'.vertexMap i x=st.vertexMap i x) ∧
      (∀ x∈p.vertices,x∉A₀ k→st'.vertexMap k x∈L) ∧
      (∀ e∈p.arcs,(e.1∈A₀ k ∧ e.2∈A₀ k) ∨ D (st'.vertexMap k e.1) (st'.vertexMap k e.2)) ∧
      p.vertices.toFinset⊆st'.assigned k ∧ p.edges⊆st'.sourceEdges k := by
  cases p with
  | path xs =>
    obtain ⟨last,hv,hvLocal,ha,haM,heM,hpres,hL,_,harcs,hvertices,hedges⟩:=
      prescribed_ordered_path_family_restricted_advance QV Q A₀ ψ E₀ J β δ hβ hβ1 hδ hδbound hnβ hn hI
        hQsize hQdegree hold hJ k Dsrc Fsrc hDQ D L hext H aScale κ θ haScale hκ hθ hH hθbudget hQlocal hδstrong hnstrong xs hp.1 hp.2 st hvalid hLocal hinit hfree hsubset
    exact ⟨last,hv,hvLocal,ha,haM,heM,hpres,hL,harcs,hvertices,hedges⟩
  | cycle a xs =>
    exact prescribed_cycle_family_restricted_advance QV Q A₀ ψ E₀ J β δ hβ hβ1 hδ hδbound hnβ hn hI
      hQsize hQdegree hold hJ k Dsrc Fsrc hDQ D L hext H aScale κ θ haScale hκ hθ hH hθbudget hQlocal hδstrong hnstrong a xs hp.1 hp.2.1 hp.2.2 st hvalid hLocal hinit hfree hsubset
end Oberwolfach
