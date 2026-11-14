module

public import Oberwolfach.OrdinaryWheelEmbeddedPacking
public import Oberwolfach.OrdinaryEmbeddedPairDegrees
public import Oberwolfach.RowCoverPackings

@[expose] public section
/-! The pulled-back packing has exactly the original rim graph and spoke
relation after embedding; in particular all row and column loads transfer. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U W Z:Type} [Fintype V] [Fintype U] [Fintype W] [Fintype Z]
  [DecidableEq V] [DecidableEq U] [DecidableEq W] [DecidableEq Z]

theorem ordinary_packing_resources_eq_host
    {Q F:SimpleGraph V} {H:V→U→Prop} {r:ℕ} (M:Finset (OrdinaryWheel Q F H r)):
    M.biUnion ordinaryWheelResources=ordinaryHostResources (ordinaryWheelRimGraph M) (ordinaryPackingSpokes M):=by
  ext a
  cases a with
  | inl e=>
    induction e using Sym2.inductionOn with
    | _ v w=>
      simp only [Finset.mem_biUnion,ordinaryWheelResources_rim,ordinaryHostResources_rim,
        SimpleGraph.mem_edgeSet,ordinaryWheelRimGraph,SimpleGraph.iSup_adj]
      constructor
      · rintro ⟨a,ha,h⟩;exact ⟨a,ha,h⟩
      · rintro ⟨a,ha,h⟩;exact ⟨a,ha,h⟩
  | inr a=>
    rcases a with ⟨v,u⟩
    simp only [Finset.mem_biUnion,ordinaryWheelResources_spoke,ordinaryHostResources_spoke,ordinaryPackingSpokes]

theorem ordinary_embedded_packing_hosts
    (φ:V↪W) (ψ:U↪Z) (G F:SimpleGraph V) (F':SimpleGraph W) (H:V→U→Prop) (r:ℕ)
    (hF:∀v w,F.Adj v w→F'.Adj (φ v) (φ w))
    (M:Finset (OrdinaryWheel (G.map φ) F' (ordinaryMappedSpokes H φ ψ) r)):
    let P:=M.image (ordinaryEmbeddedWheelPullback φ ψ G F F' H r hF);
    (ordinaryWheelRimGraph P).map φ=ordinaryWheelRimGraph M ∧
    ordinaryMappedSpokes (ordinaryPackingSpokes P) φ ψ=ordinaryPackingSpokes M:=by
  intro P
  have he:=ordinary_embedded_packing_resources φ ψ G F F' H r hF M
  change (P.biUnion ordinaryWheelResources).image (ordinaryPairResourceEmbedding φ ψ)=M.biUnion ordinaryWheelResources at he
  rw [ordinary_packing_resources_eq_host,ordinary_packing_resources_eq_host,
    ordinaryHostResources_embedding_image] at he
  constructor
  · ext v w
    have hh:=congrArg (fun S:Finset (Sym2 W⊕(W×Z))=>Sum.inl s(v,w)∈S) he
    simpa only [ordinaryHostResources_rim,SimpleGraph.mem_edgeSet] using (Iff.of_eq hh)
  · funext v u
    apply propext
    have hh:=congrArg (fun S:Finset (Sym2 W⊕(W×Z))=>Sum.inr (v,u)∈S) he
    simpa only [ordinaryHostResources_spoke] using (Iff.of_eq hh)
end Oberwolfach
