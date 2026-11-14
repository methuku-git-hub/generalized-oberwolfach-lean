module

public import Oberwolfach.EndpointFactorGraphChoice
public import Oberwolfach.SelectionCandidateBudget

@[expose] public section

/-! Select physical edge-disjoint local factors and retain their original
cycle identifiers. This deterministic step is used only after its robust
single-factor input has been constructed on the common sampling event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem select_endpoint_factors (p:ℝ) (hp:0<p):
    ∃ N:ℕ,∀ (V:Type) [Fintype V] [DecidableEq V],N≤Fintype.card V→
    ∀ (L:ℕ) (Q F:SimpleGraph V) (S T Y:Fin L→Finset V) (hST:∀ i,Disjoint (S i) (T i)),
    (∀ i j,i≠j→((Y i∩Y j).card:ℝ)≤p^2*Fintype.card V)→
    (∀ v,((Finset.univ.filter (fun i=>v∈Y i)).card:ℝ)≤p*Fintype.card V)→
    (∀ i,∀ K:SimpleGraph V,K≤spanningRestriction Q (Y i)→
      (∀ v,(K.degree v:ℝ)≤2*(p*Real.sqrt p*Fintype.card V)+
        2*(Nat.ceil (4*(p*Real.sqrt p*Fintype.card V)):ℝ))→
      ∃ D:Finset (EndpointTriangle Q F (S i) (T i)),
        ((∀ C∈D,∀ E∈D,C≠E→Disjoint (endpointTriangleVertices C) (endpointTriangleVertices E)) ∧
          D.biUnion endpointTriangleVertices=Y i) ∧
        endpointFactorGraph (hST i) D≤spanningRestriction Q (Y i) ∧
        (∀ v,(endpointFactorGraph (hST i) D).degree v≤2) ∧ Disjoint (endpointFactorGraph (hST i) D) K)→
    ∃ D:∀ i,Finset (EndpointTriangle Q F (S i) (T i)),
      (∀ i,(∀ C∈D i,∀ E∈D i,C≠E→Disjoint (endpointTriangleVertices C) (endpointTriangleVertices E)) ∧
        (D i).biUnion endpointTriangleVertices=Y i) ∧
      (∀ i j,i≠j→Disjoint (endpointFactorGraph (hST i) (D i)) (endpointFactorGraph (hST j) (D j))) ∧
      ∀ v,((⨆ i,endpointFactorGraph (hST i) (D i)).degree v:ℝ)≤2*(p*Fintype.card V):=by
  obtain ⟨N,hN,hselect⟩:=bounded_degree_selection_from_single_copy p hp
  refine ⟨N,?_⟩
  intro V _ _ hn L Q F S T Y hST hinter hmem hsingle
  let family:Fin L→Set (SimpleGraph V):=fun i G=>∃ D:Finset (EndpointTriangle Q F (S i) (T i)),
    ((∀ C∈D,∀ E∈D,C≠E→Disjoint (endpointTriangleVertices C) (endpointTriangleVertices E)) ∧
      D.biUnion endpointTriangleVertices=Y i) ∧ endpointFactorGraph (hST i) D=G
  have hchoice (i:Fin L) (K:SimpleGraph V) (hK:K≤spanningRestriction Q (Y i))
      (hdeg:∀ v,(K.degree v:ℝ)≤(2:ℕ)*(p*Real.sqrt p*Fintype.card V)+
        (2:ℕ)*(Nat.ceil (4*(p*Real.sqrt p*Fintype.card V)):ℝ)):
      ∃ G:SimpleGraph V,G∈family i ∧ G≤spanningRestriction Q (Y i) ∧
        (∀ v,G.degree v≤2) ∧ Disjoint G K:=by
    obtain ⟨D,hD,hsub,hdegree,havoid⟩:=hsingle i K hK (by simpa only [Nat.cast_ofNat] using hdeg)
    exact ⟨endpointFactorGraph (hST i) D,⟨D,hD,rfl⟩,hsub,hdegree,havoid⟩
  obtain ⟨G,hG,hdis,hdegree⟩:=hselect V hn L 2 Q Y family hinter hmem hchoice
  have hrep (i:Fin L):∃ D:Finset (EndpointTriangle Q F (S i) (T i)),
      ((∀ C∈D,∀ E∈D,C≠E→Disjoint (endpointTriangleVertices C) (endpointTriangleVertices E)) ∧
        D.biUnion endpointTriangleVertices=Y i) ∧ endpointFactorGraph (hST i) D=G i:=(hG i).1
  choose D hD using hrep
  refine ⟨D,fun i=>(hD i).1,?_,?_⟩
  · intro i j hij;rw [(hD i).2,(hD j).2];exact hdis i j hij
  · intro v
    have he:(⨆ i,endpointFactorGraph (hST i) (D i))=(⨆ i,G i):=iSup_congr (fun i=>(hD i).2)
    rw [he]
    simpa only [Nat.cast_ofNat] using hdegree v

end Oberwolfach
