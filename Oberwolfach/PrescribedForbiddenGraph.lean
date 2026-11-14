module

public import Oberwolfach.PrescribedEmbeddingFamilyUsedDegree

@[expose] public section
/-! Construct the forbidden physical graph as the union of all current factor
edge images and the separately reserved graph, with the required degree bound. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V I:Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

theorem prescribed_forbidden_graph_from_partial_images
    (X:I→Type) [∀ i,Fintype (X i)] (Q:∀ i,SimpleGraph (X i))
    (φ:∀ i,X i↪V) (H:I→SimpleGraph V) (old fresh:I→V→Prop)
    (hsource:∀ i,H i≤(Q i).map (φ i)) (hsourceDegree:∀ i x,(Q i).degree x≤2)
    (hocc:∀ i v,(∃ x,φ i x=v)→ old i v ∨ fresh i v)
    (J:SimpleGraph V) (δ n t:ℝ)
    (hold:∀ v,((Finset.univ.filter (fun i=>old i v)).card:ℝ)≤δ*n)
    (hfresh:∀ v,((Finset.univ.filter (fun i=>fresh i v)).card:ℝ)≤t+1)
    (hJ:∀ v,(J.degree v:ℝ)≤δ*n):
    let G:SimpleGraph V:=⨆ i,H i;
    let F:=G⊔J;
    letI : DecidableRel F.Adj := fun _ _=>Classical.propDecidable _;
    (∀ v,(G.degree v:ℝ)≤2*δ*n+2*t+2 ∧ (F.degree v:ℝ)≤3*δ*n+2*t+2) ∧
    (∀ i,(H i).edgeFinset⊆F.edgeFinset) ∧ J.edgeFinset⊆F.edgeFinset := by
  intro G F
  letI : DecidableRel F.Adj := fun _ _=>Classical.propDecidable _
  have hcover:∀ v,G.neighborFinset v⊆Finset.univ.biUnion (fun i=>(H i).neighborFinset v):=by
    intro v w hw
    simp only [SimpleGraph.mem_neighborFinset] at hw
    change (⨆ i,H i).Adj v w at hw
    obtain ⟨i,hi⟩:=SimpleGraph.iSup_adj.mp hw
    simp only [Finset.mem_biUnion,Finset.mem_univ,true_and,SimpleGraph.mem_neighborFinset]
    exact ⟨i,hi⟩
  have hforbid:∀ v,F.neighborFinset v⊆G.neighborFinset v∪J.neighborFinset v:=by
    intro v w hw
    simp only [SimpleGraph.mem_neighborFinset] at hw
    change (G⊔J).Adj v w at hw
    simp only [Finset.mem_union,SimpleGraph.mem_neighborFinset,SimpleGraph.sup_adj]
    exact (SimpleGraph.sup_adj G J v w).mp hw
  have hbound:=prescribed_embedding_used_degree_from_partial_images X Q φ H old fresh hsource hsourceDegree hocc G J F hcover hforbid δ n t hold hfresh hJ
  refine ⟨hbound,?_,?_⟩
  · intro i
    apply SimpleGraph.edgeFinset_mono
    intro v w hw
    change (G⊔J).Adj v w
    apply (SimpleGraph.sup_adj G J v w).mpr
    left
    change (⨆ i,H i).Adj v w
    exact SimpleGraph.iSup_adj.mpr ⟨i,hw⟩
  · apply SimpleGraph.edgeFinset_mono
    intro v w hw
    change (G⊔J).Adj v w
    exact (SimpleGraph.sup_adj G J v w).mpr (Or.inr hw)
end Oberwolfach
