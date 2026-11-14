module

public import Oberwolfach.FirstVortexCompletionProtectsReserve

@[expose] public section
/-! The actual old edges and the prescribed completion both avoid the same
fixed reservoir, provided the used matching and the permitted arcs avoid it. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstVortexWholeReserveGeneralFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_completion_whole_packing_protects_reserve_general
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (Dsrc:U→Fin n→Fin n→Prop)
    (K J:U→Type) [∀w,DecidableEq (K w)] [∀w,DecidableEq (J w)]
    (a:∀w,ActualResidualData (K:=K w) (J:=J w) (F w))
    (Interiors:U→Finset (Fin n)) (ψ:U→Fin n→Fin n)
    (Kbad Jbad Used R:SimpleGraph (Fin n)) (Lbad:Sym2 (Fin n)→Finset U)
    (Bad:Fin n→Finset U) (Z:U→Finset (Fin n))
    (Dfree Dstar:Fin n→Fin n→Prop) (Pack:Finset (Sym2 (Fin n)))
    (Lists:U→Finset (Fin n)) (FinalEdges:U→Finset (Sym2 (Fin n))) (δ:ℝ)
    (hPack:Pack⊆Used.edgeFinset)
    (hUsed:∀x y,Used.Adj x y→¬R.Adj x y)
    (hD:∀x y,Dstar x y→¬R.Adj x y):
    FirstVortexResidualCompletion F Dsrc K J a Interiors ψ Kbad Jbad Lbad Bad Z Dfree
      Dstar Pack Lists FinalEdges δ→
    ∃E:U→Finset (Sym2 (Fin n)),Kbad.edgeFinset⊆Finset.univ.biUnion E ∧
      (∀i,Disjoint (E i) Jbad.edgeFinset) ∧ (∀i,Disjoint (E i) Pack) ∧
      (∀v,((prescribedPhysicalUnion E).degree v:ℝ)≤5*Real.sqrt δ*Fintype.card (Fin n)) ∧
      (∀x y,(SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 (Fin n)))⊔prescribedPhysicalUnion E).Adj x y→¬R.Adj x y):=by
  intro hcompletion
  obtain ⟨E,hcover,hJ,hOld,hdegree,hreserve⟩:=first_vortex_completion_protects_reserve F Dsrc K J a Interiors ψ
    Kbad Jbad R Lbad Bad Z Dfree Dstar Pack Lists FinalEdges δ hD hcompletion
  refine ⟨E,hcover,hJ,hOld,hdegree,?_⟩
  intro x y h
  rcases h with h|h
  · exact hUsed x y (SimpleGraph.mem_edgeFinset.mp (hPack ((SimpleGraph.fromEdgeSet_adj _).mp h).1))
  · exact hreserve x y h
end Oberwolfach
