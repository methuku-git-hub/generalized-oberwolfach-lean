module

public import Oberwolfach.OrdinaryActualDiagramModels

@[expose] public section

/-! Every expansion in the actual five-graph absorber diagram satisfies
row balance and hub divisibility. The comparison graph is obtained from the
original divisibility hypotheses, not from an assumed original decomposition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V₀ U₀:Type} [Fintype V₀] [Fintype U₀] [DecidableEq V₀] [DecidableEq U₀]

theorem ordinary_actual_diagram_divisibility (G:SimpleGraph V₀) (Hs:V₀→U₀→Prop)
    (r:ℕ) (hr:3≤r)
    (hbal:∀ v,G.degree v=2*(Finset.univ.filter (Hs v)).card)
    (hdiv:∀ u,r∣(Finset.univ.filter (fun v=>Hs v u)).card) :
    ∀ i:Fin 3,
      (∀ a,(ordinaryDiagramExpansionRim G Hs r hr i).degree a=
        2*(Finset.univ.filter (ordinaryDiagramExpansionSpokes G Hs r hr i a)).card)∧
      (∀ b,r∣(Finset.univ.filter (fun a=>ordinaryDiagramExpansionSpokes G Hs r hr i a b)).card) := by
  have hC:(SimpleGraph.cycleGraph r).IsRegularOfDegree 2:=by
    intro a
    simpa only [←SimpleGraph.ncard_neighborSet] using cycleGraph_regular hr a
  let z:Fin r:=⟨0,by omega⟩
  let o:Fin r:=⟨r-1,by omega⟩
  have hzo:(SimpleGraph.cycleGraph r).Adj z o:=cycleGraph_zero_last_adj r hr
  have h0:=actual_edge_spoke_expansion_balance (SimpleGraph.cycleGraph r) z o hzo (by intro a;simpa only [←SimpleGraph.ncard_neighborSet] using cycleGraph_regular hr a) G Hs hbal
  have h0':=actual_edge_spoke_expansion_divisibility (W:=Fin r) G Hs r (Fintype.card_fin r) z hdiv
  have h1:=original_central_cycle_divisible G Hs r hr hbal hdiv
  let k:=G.edgeFinset.card/r
  let Gc:=ordinaryComparisonRim r k (by omega)
  let Hc:=ordinaryComparisonSpokes r k (by omega)
  have hc:=ordinary_comparison_from_divisibility G Hs r hr hbal hdiv
  have h2:=actual_edge_spoke_expansion_balance (SimpleGraph.cycleGraph r) z o hzo (by intro a;simpa only [←SimpleGraph.ncard_neighborSet] using cycleGraph_regular hr a) Gc Hc hc.2.1
  have h2':=actual_edge_spoke_expansion_divisibility (W:=Fin r) Gc Hc r (Fintype.card_fin r) z hc.2.2.1
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i=>Fin.elim0 i)))
  · simpa [ordinaryDiagramExpansionRim,ordinaryDiagramExpansionSpokes,ordinaryDiagramOldRows,ordinaryDiagramOldHubs,ordinaryDiagramEdges,ordinaryDiagramSpokes,ordinaryDiagramX,ordinaryDiagramY,ordinaryDiagramV,ordinaryDiagramU,ordinaryDiagramOldRows_fintype,ordinaryDiagramOldHubs_fintype,ordinaryDiagramEdges_fintype,ordinaryDiagramSpokes_fintype,Fin.cases,Fin.induction,Fin.induction.go,z,o,Gc,Hc,k,←SimpleGraph.ncard_neighborSet] using And.intro h0 h0'
  · simpa [ordinaryDiagramExpansionRim,ordinaryDiagramExpansionSpokes,ordinaryDiagramOldRows,ordinaryDiagramOldHubs,ordinaryDiagramEdges,ordinaryDiagramSpokes,ordinaryDiagramX,ordinaryDiagramY,ordinaryDiagramV,ordinaryDiagramU,ordinaryDiagramOldRows_fintype,ordinaryDiagramOldHubs_fintype,ordinaryDiagramEdges_fintype,ordinaryDiagramSpokes_fintype,Fin.cases,Fin.induction,Fin.induction.go,z,o,Gc,Hc,k,←SimpleGraph.ncard_neighborSet] using h1
  · simpa [ordinaryDiagramExpansionRim,ordinaryDiagramExpansionSpokes,ordinaryDiagramOldRows,ordinaryDiagramOldHubs,ordinaryDiagramEdges,ordinaryDiagramSpokes,ordinaryDiagramX,ordinaryDiagramY,ordinaryDiagramV,ordinaryDiagramU,ordinaryDiagramOldRows_fintype,ordinaryDiagramOldHubs_fintype,ordinaryDiagramEdges_fintype,ordinaryDiagramSpokes_fintype,Fin.cases,Fin.induction,Fin.induction.go,z,o,Gc,Hc,k,←SimpleGraph.ncard_neighborSet] using And.intro h2 h2'

end Oberwolfach
