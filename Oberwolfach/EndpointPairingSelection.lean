module

public import Oberwolfach.EndpointPairingGraph
public import Oberwolfach.IndexedGraphSelection

@[expose] public section

/-! Simultaneous selection keeps the actual endpoint pairings as witnesses.
The bounded-degree single-copy premise is discharged by the fresh-sampling
result at the probabilistic caller. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem select_endpoint_pairings (p:ℝ) (hp:0<p):
    ∃ N:ℕ,∀ (V J:Type) [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J],N≤Fintype.card V→
    ∀ (Q F:SimpleGraph V) (A B:J→Finset V),
    (∀ i j,i≠j→(((A i∪B i)∩(A j∪B j)).card:ℝ)≤p^2*Fintype.card V)→
    (∀ v,((Finset.univ.filter (fun j=>v∈A j∪B j)).card:ℝ)≤p*Fintype.card V)→
    (∀ j,∀ K:SimpleGraph V,K≤spanningRestriction Q (A j∪B j)→
      (∀ v,(K.degree v:ℝ)≤2*(p*Real.sqrt p*Fintype.card V)+
        2*(Nat.ceil (4*(p*Real.sqrt p*Fintype.card V)):ℝ))→
      ∃ P:EndpointPairing Q F (A j) (B j),Disjoint P.graph K)→
    ∃ P:∀ j,EndpointPairing Q F (A j) (B j),
      (∀ i j,i≠j→Disjoint (P i).graph (P j).graph) ∧
      ∀ v,((⨆ j,(P j).graph).degree v:ℝ)≤2*(p*Fintype.card V):=by
  obtain ⟨N,hN⟩:=bounded_degree_selection_indexed p hp
  refine ⟨N,?_⟩
  intro V J _ _ _ _ hn Q F A B hinter hmem hsingle
  let family:J→Set (SimpleGraph V):=fun j G=>∃ P:EndpointPairing Q F (A j) (B j),P.graph=G
  have hchoice (j:J) (K:SimpleGraph V) (hK:K≤spanningRestriction Q (A j∪B j))
      (hdeg:∀ v,(K.degree v:ℝ)≤(2:ℕ)*(p*Real.sqrt p*Fintype.card V)+
        (2:ℕ)*(Nat.ceil (4*(p*Real.sqrt p*Fintype.card V)):ℝ)):
      ∃ G:SimpleGraph V,G∈family j ∧ G≤spanningRestriction Q (A j∪B j) ∧
        (∀ v,G.degree v≤2) ∧ Disjoint G K:=by
    obtain ⟨P,hP⟩:=hsingle j K hK (by simpa only [Nat.cast_ofNat] using hdeg)
    exact ⟨P.graph,⟨P,rfl⟩,P.graph_le,P.graph_degree,hP⟩
  obtain ⟨G,hG,hdis,hdeg⟩:=hN V J hn 2 Q (fun j=>A j∪B j) family hinter hmem hchoice
  have hrep (j:J):∃ P:EndpointPairing Q F (A j) (B j),P.graph=G j:=(hG j).1
  choose P hP using hrep
  refine ⟨P,?_,?_⟩
  · intro i j hij;rw [hP,hP];exact hdis i j hij
  · intro v
    have he:(⨆ j,(P j).graph)=⨆ j,G j:=iSup_congr hP
    rw [he];simpa only [Nat.cast_ofNat] using hdeg v

end Oberwolfach
