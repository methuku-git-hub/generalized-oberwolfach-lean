module

public import Oberwolfach.PrescribedOrderedPathFamilyAdvance
public import Oberwolfach.PrescribedCycleFamilyAdvance

@[expose] public section
/-! Paths and cycles as explicitly ordered source components. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X:Type} [DecidableEq X]

inductive PrescribedSourcePiece (X:Type) where
  | path (vertices:List X)
  | cycle (first:X) (rest:List X)

def PrescribedSourcePiece.vertices:PrescribedSourcePiece X→List X
  | .path xs=>xs
  | .cycle a xs=>a::xs

def PrescribedSourcePiece.edges:PrescribedSourcePiece X→Finset (Sym2 X)
  | .path xs=>prescribedOrderedPathEdges xs
  | .cycle a xs=>prescribedOrderedPathEdges ((a::xs)++[a])

def PrescribedSourcePiece.arcs:PrescribedSourcePiece X→Finset (X×X)
  | .path xs=>prescribedDirectedPathEdges xs
  | .cycle a xs=>prescribedDirectedPathEdges ((a::xs)++[a])

def PrescribedSourcePiece.Valid (p:PrescribedSourcePiece X) (D:X→X→Prop) (F:SimpleGraph X):Prop:=
  match p with
  | .path xs=>xs.Nodup ∧ List.IsChain (fun x y=>D x y ∧ ¬F.Adj x y) xs
  | .cycle a xs=>(a::xs).Nodup ∧ 3≤(a::xs).length ∧ DirectedCycleThrough D F (a::xs)

theorem prescribed_source_piece_arc_endpoints (p:PrescribedSourcePiece X) (e:X×X)
    (he:e∈p.arcs):e.1∈p.vertices ∧ e.2∈p.vertices := by
  cases p with
  | path xs =>exact prescribed_directed_path_edge_endpoints xs e he
  | cycle a xs =>
    have hh:=prescribed_directed_path_edge_endpoints ((a::xs)++[a]) e he
    change e.1∈a::xs ∧ e.2∈a::xs
    simpa [or_assoc,or_left_comm,or_comm] using hh

variable {I V:Type} [Fintype I] [Fintype X] [Fintype V] [DecidableEq I] [DecidableEq V]

theorem prescribed_source_piece_advance
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
    (p:PrescribedSourcePiece X) (hp:p.Valid Dsrc Fsrc) (st:PrescribedFamilyState I X V)
    (hvalid:st.Valid QV Q A₀ ψ E₀ J (Real.sqrt δ*Fintype.card V))
    (hinit:prescribedInducedSourceEdges (Q k) (A₀ k)⊆st.sourceEdges k)
    (hfree:∀ x∈p.vertices,x∉A₀ k→x∉st.assigned k) (hsubset:∀ x∈p.vertices,x∈QV k):
    ∃ st':PrescribedFamilyState I X V,
      st'.Valid QV Q A₀ ψ E₀ J (Real.sqrt δ*Fintype.card V) ∧
      st'.assigned=Function.update st.assigned k (st.assigned k∪p.vertices.toFinset) ∧
      (∀ i,st.assigned i⊆st'.assigned i) ∧ (∀ i,st.sourceEdges i⊆st'.sourceEdges i) ∧
      (∀ i x,x∈st.assigned i→st'.vertexMap i x=st.vertexMap i x) ∧
      (∀ x∈p.vertices,x∉A₀ k→st'.vertexMap k x∈L) ∧
      (∀ e∈p.arcs,(e.1∈A₀ k ∧ e.2∈A₀ k) ∨ D (st'.vertexMap k e.1) (st'.vertexMap k e.2)) ∧
      p.vertices.toFinset⊆st'.assigned k ∧ p.edges⊆st'.sourceEdges k := by
  cases p with
  | path xs =>
    obtain ⟨last,hv,ha,haM,heM,hpres,hL,_,harcs,hvertices,hedges⟩:=
      prescribed_ordered_path_family_advance QV Q A₀ ψ E₀ J β δ hβ hβ1 hδ hδbound hnβ hn hI
        hQsize hQdegree hold hJ k Dsrc Fsrc hDQ D L hext xs hp.1 hp.2 st hvalid hinit hfree hsubset
    exact ⟨last,hv,ha,haM,heM,hpres,hL,harcs,hvertices,hedges⟩
  | cycle a xs =>
    exact prescribed_cycle_family_advance QV Q A₀ ψ E₀ J β δ hβ hβ1 hδ hδbound hnβ hn hI
      hQsize hQdegree hold hJ k Dsrc Fsrc hDQ D L hext a xs hp.1 hp.2.1 hp.2.2 st hvalid hinit hfree hsubset
end Oberwolfach
