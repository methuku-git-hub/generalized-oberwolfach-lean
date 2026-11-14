module

public import Oberwolfach.ActualResidualHostContainment
public import Oberwolfach.TwoFactorEmbeddingDecomposition

@[expose] public section
/-! A completed actual residual family gives precisely the manuscript's
factor decomposition once its verified old and new embeddings lie in the
regular host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {K J:Type} [DecidableEq K] [DecidableEq J]

theorem actual_glued_residuals_give_factor_decomposition {n D:ℕ}
    (hEven:Even D) (G:SimpleGraph (Fin n)) (hG:G.IsRegularOfDegree D)
    (F:Fin (D/2)→SimpleGraph (Fin n)) (hF:∀i,(F i).IsRegularOfDegree 2)
    (a:∀i,ActualResidualData (K:=K) (J:=J) (F i))
    (pieces:∀i,List (PrescribedSourcePiece {x // x∈(a i).remaining}))
    (hgraph:∀i,prescribedDependentGraph pieces i=((a i).graph).induce (↑(a i).remaining:Set (Fin n)))
    (hCycle:∀i,(a i).t.biUnion (fun j=>((a i).C j).support.toFinset)⊆(a i).Cembed)
    (ψ h:Fin (D/2)→Fin n→Fin n) (Φ:∀i,{x // x∈(a i).remaining}→Fin n)
    (hinj:∀i,Function.Injective (h i))
    (hold:∀i x,x∈(a i).oldDomain→h i x=ψ i x)
    (hrem:∀i (x:{x // x∈(a i).remaining}),h i x.1=Φ i x)
    (Dstar:Fin n→Fin n→Prop) (harc:∀i x y,prescribedDependentDigraph pieces i x y→Dstar (Φ i x) (Φ i y))
    (Pack:Finset (Sym2 (Fin n)))
    (hOld:PairwisePhysicalDisjoint (fun i=>((a i).deletedEdges).image (Sym2.map (ψ i))))
    (hOldPack:∀i,((a i).deletedEdges).image (Sym2.map (ψ i))⊆Pack)
    (hNew:PairwisePhysicalDisjoint (fun i=>((prescribedDependentGraph pieces i).edgeFinset).image (Sym2.map (Φ i))))
    (hNewPack:∀i,Disjoint (((prescribedDependentGraph pieces i).edgeFinset).image (Sym2.map (Φ i))) Pack)
    (hPackHost:Pack⊆G.edgeFinset) (hhost:∀x y,Dstar x y→G.Adj x y):
    HasFactorDecomposition G F :=by
  have hsub:=actual_glued_factor_images_in_host F hF a pieces hgraph hCycle ψ h Φ hold hrem Dstar harc Pack hOldPack G hPackHost hhost
  have hpair:PairwisePhysicalDisjoint (fun i=>((F i).edgeFinset).image (Sym2.map (h i))) :=
    (actual_piece_family_glued_physical_edges F hF a pieces hgraph hCycle ψ h Φ hold hrem Pack ∅ hOld hOldPack hNew hNewPack (by simp)).1
  exact even_regular_two_factor_embeddings_give_decomposition hEven G hG F hF h hinj hsub hpair
end Oberwolfach
