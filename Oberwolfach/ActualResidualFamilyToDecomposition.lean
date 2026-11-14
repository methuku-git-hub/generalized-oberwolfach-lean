module

public import Oberwolfach.ResidualActualEdgePartition
public import Oberwolfach.TwoFactorEmbeddingDecomposition

@[expose] public section
/-! The actual residual-family output gives an exact decomposition once its
old and new physical edges lie in the regular host and the completed factors
are pairwise edge-disjoint. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_residual_family_gives_decomposition
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
    (hNewHost:∀i,(((a i).graph.induce (↑(a i).remaining:Set (Fin n))).edgeFinset).image
      (Sym2.map (Φ i))⊆H.edgeFinset)
    (hdis:PairwisePhysicalDisjoint (fun i=>((F i).edgeFinset).image (Sym2.map (f i)))) :
    HasFactorDecomposition H F := by
  apply even_regular_two_factor_embeddings_give_decomposition hEven H hH F hF f hinj ?_ hdis
  intro i
  rw [(a i).glued_factor_edge_images (hF i) (hCycle i) (ψ i) (f i) (Φ i) (hold i) (hrem i)]
  exact Finset.union_subset ((hOldPack i).trans hPackHost) (hNewHost i)
end Oberwolfach
