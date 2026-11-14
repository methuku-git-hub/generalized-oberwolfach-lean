module

public import Oberwolfach.FirstVortexResidualCompletion
public import Oberwolfach.PrescribedFamilyAvoidPhysicalGraph

@[expose] public section
/-! Extract the actual prescribed edge family from the residual completion and
show it avoids a reserved physical graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstVortexCompletionProtectsReserveFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_completion_protects_reserve
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (Dsrc:U→Fin n→Fin n→Prop)
    (K J:U→Type) [∀w,DecidableEq (K w)] [∀w,DecidableEq (J w)]
    (a:∀w,ActualResidualData (K:=K w) (J:=J w) (F w))
    (Interiors:U→Finset (Fin n)) (ψ:U→Fin n→Fin n)
    (Kbad Jbad R:SimpleGraph (Fin n)) (Lbad:Sym2 (Fin n)→Finset U)
    (Bad:Fin n→Finset U) (Z:U→Finset (Fin n))
    (Dfree Dstar:Fin n→Fin n→Prop) (Pack:Finset (Sym2 (Fin n)))
    (Lists:U→Finset (Fin n)) (FinalEdges:U→Finset (Sym2 (Fin n))) (δ:ℝ)
    (hD:∀x y,Dstar x y→¬R.Adj x y):
    FirstVortexResidualCompletion F Dsrc K J a Interiors ψ Kbad Jbad Lbad Bad Z Dfree Dstar Pack Lists FinalEdges δ→
    ∃E:U→Finset (Sym2 (Fin n)),Kbad.edgeFinset⊆Finset.univ.biUnion E ∧
      (∀i,Disjoint (E i) Jbad.edgeFinset) ∧ (∀i,Disjoint (E i) Pack) ∧
      (∀v,((prescribedPhysicalUnion E).degree v:ℝ)≤5*Real.sqrt δ*Fintype.card (Fin n)) ∧
      (∀x y,(prescribedPhysicalUnion E).Adj x y→¬R.Adj x y):=by
  intro hcompletion
  rcases hcompletion with ⟨pieces,hgraph,harcs,assign,orient,B,g,Φ,fC,hOld,hΦ,hB,hbad,hlist,hΦg,hZ,hLists,hDstar,hpair,hcover,hJ,hPack,hdis,hload,hunion,hdegree⟩
  let E:=fun i=>((prescribedDependentGraph pieces i).edgeFinset).image (Sym2.map (Φ i))
  refine ⟨E,hcover,hJ,hPack,hdegree,?_⟩
  apply prescribed_family_avoids_physical_graph pieces Φ Dstar R ?_ hD
  intro i x y h
  exact (hDstar i x y h).1
end Oberwolfach
