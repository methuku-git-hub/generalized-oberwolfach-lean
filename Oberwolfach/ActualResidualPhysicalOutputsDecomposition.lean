module

public import Oberwolfach.ActualDirectedResidualToDecomposition
public import Oberwolfach.ResidualActualCompletedPieceFamily

@[expose] public section
/-! Consume the original residual embedding outputs to obtain the exact
regular-host decomposition, deriving full-factor edge disjointness. -/
set_option autoImplicit false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_residual_physical_outputs_give_decomposition
    {n D:ℕ} {K J:Type} [DecidableEq K] [DecidableEq J]
    (hEven:Even D) (H:SimpleGraph (Fin n)) (hH:H.IsRegularOfDegree D)
    (F:Fin (D/2)→SimpleGraph (Fin n)) (hF:∀i,(F i).IsRegularOfDegree 2)
    (a:∀i,ActualResidualData (K:=K) (J:=J) (F i))
    (hCycle:∀i,(a i).t.biUnion (fun j=>((a i).C j).support.toFinset)⊆(a i).Cembed)
    (ψ f:Fin (D/2)→Fin n→Fin n)
    (Φ:∀i,{x // x∈(a i).remaining}→Fin n)
    (hinj:∀i,Function.Injective (f i))
    (hold:∀i x,x∈(a i).oldDomain→f i x=ψ i x)
    (hrem:∀i (x:{x // x∈(a i).remaining}),f i x.val=Φ i x)
    (Pack:Finset (Sym2 (Fin n)))
    (hOldPack:∀i,(a i).deletedEdges.image (Sym2.map (ψ i))⊆Pack)
    (hPackHost:Pack⊆H.edgeFinset)
    (pieces:∀i,List (PrescribedSourcePiece {x // x∈(a i).remaining}))
    (hgraph:∀i,prescribedDependentGraph pieces i=((a i).graph).induce (↑(a i).remaining:Set (Fin n)))
    (Dstar:Fin n→Fin n→Prop) (hHost:∀x y,Dstar x y→H.Adj x y)
    (harc:∀i x y,prescribedDependentDigraph pieces i x y→Dstar (Φ i x) (Φ i y))
    (hOld:PairwisePhysicalDisjoint (fun i=>((a i).deletedEdges).image (Sym2.map (ψ i))))
    (hNew:PairwisePhysicalDisjoint (fun i=>((prescribedDependentGraph pieces i).edgeFinset).image (Sym2.map (Φ i))))
    (hNewPack:∀i,Disjoint (((prescribedDependentGraph pieces i).edgeFinset).image (Sym2.map (Φ i))) Pack) : HasFactorDecomposition H F := by
  have hdis:PairwisePhysicalDisjoint (fun i=>((F i).edgeFinset).image (Sym2.map (f i))):=
    (actual_piece_family_glued_physical_edges F hF a pieces hgraph hCycle ψ f Φ hold hrem Pack ∅
      hOld hOldPack hNew hNewPack (Finset.empty_subset _)).1
  exact actual_directed_residual_family_gives_decomposition hEven H hH F hF a hCycle ψ f Φ hinj hold hrem
    Pack hOldPack hPackHost pieces hgraph Dstar hHost harc hdis
end Oberwolfach
