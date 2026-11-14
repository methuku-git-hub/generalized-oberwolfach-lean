module

public import Oberwolfach.MappedFactorGraph
public import Oberwolfach.IndexedGraphSelection
public import Oberwolfach.EndpointPairingGraph

@[expose] public section

/-! Joint selection retains avoidance of an already used physical graph.
Its two single-copy inputs explicitly retain that same avoidance guarantee. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem select_mixed_boundary_pairings_avoiding (p:ℝ) (hp:0<p):
    ∃ N:ℕ,∀ (V W J K:Type) [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
      [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K],N≤Fintype.card W→
    ∀ (r:ℕ) (Q F:SimpleGraph V) (P B Z:SimpleGraph W) (e:V↪W),Q.map e≤P→
    ∀ (T Y:J→Finset V) (S U:K→Finset W),
    (∀ i j:J⊕K,i≠j→
      ((Sum.elim (fun j=>(Y j).image e) (fun k=>S k∪U k) i∩
        Sum.elim (fun j=>(Y j).image e) (fun k=>S k∪U k) j).card:ℝ)≤p^2*Fintype.card W)→
    (∀ w,((Finset.univ.filter (fun i:J⊕K=>w∈Sum.elim (fun j=>(Y j).image e) (fun k=>S k∪U k) i)).card:ℝ)
      ≤p*Fintype.card W)→
    (∀ j,∀ H:SimpleGraph V,
      (∀ v,(H.degree v:ℝ)≤2*(p*Real.sqrt p*Fintype.card W)+
        2*(Nat.ceil (4*(p*Real.sqrt p*Fintype.card W)):ℝ))→
      ∃ D:Finset (LocalOrdinaryCycle Q F (T j) r),
        ((∀ C∈D,∀ E∈D,C≠E→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices E)) ∧
          D.biUnion localOrdinaryVertices=Y j) ∧ Disjoint (localOrdinaryFactorGraph D) H ∧ Disjoint ((localOrdinaryFactorGraph D).map e) Z)→
    (∀ k,∀ H:SimpleGraph W,
      (∀ w,(H.degree w:ℝ)≤2*(p*Real.sqrt p*Fintype.card W)+
        2*(Nat.ceil (4*(p*Real.sqrt p*Fintype.card W)):ℝ))→
      ∃ E:EndpointPairing P B (S k) (U k),Disjoint E.graph H ∧ Disjoint E.graph Z)→
    ∃ D:∀ j,Finset (LocalOrdinaryCycle Q F (T j) r),
    ∃ E:∀ k,EndpointPairing P B (S k) (U k),
      (∀ j,(∀ C∈D j,∀ C'∈D j,C≠C'→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices C')) ∧
        (D j).biUnion localOrdinaryVertices=Y j) ∧
      let G:J⊕K→SimpleGraph W:=Sum.elim
        (fun j=>(localOrdinaryFactorGraph (D j)).map e) (fun k=>(E k).graph)
      (∀ i,G i≤spanningRestriction P (Sum.elim (fun j=>(Y j).image e) (fun k=>S k∪U k) i)) ∧
      (∀ i j,i≠j→Disjoint (G i) (G j)) ∧
      (∀ i,Disjoint (G i) Z) ∧
      ∀ w,((⨆ i,G i).degree w:ℝ)≤2*(p*Fintype.card W):=by
  obtain ⟨N,hN⟩:=bounded_degree_selection_indexed p hp
  refine ⟨N,?_⟩
  intro V W J K _ _ _ _ _ _ _ _ hn r Q F P B Z e hQ T Y S U hinter hmem ho he
  let family:J⊕K→Set (SimpleGraph W):=Sum.elim
    (fun j G=>∃ D:Finset (LocalOrdinaryCycle Q F (T j) r),
      ((∀ C∈D,∀ E∈D,C≠E→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices E)) ∧
        D.biUnion localOrdinaryVertices=Y j) ∧ (localOrdinaryFactorGraph D).map e=G ∧ Disjoint G Z)
    (fun k G=>∃ E:EndpointPairing P B (S k) (U k),E.graph=G ∧ Disjoint G Z)
  have hchoice (i:J⊕K) (H:SimpleGraph W)
      (_hH:H≤spanningRestriction P (Sum.elim (fun j=>(Y j).image e) (fun k=>S k∪U k) i))
      (hdeg:∀ w,(H.degree w:ℝ)≤(2:ℕ)*(p*Real.sqrt p*Fintype.card W)+
        (2:ℕ)*(Nat.ceil (4*(p*Real.sqrt p*Fintype.card W)):ℝ)):
      ∃ G:SimpleGraph W,G∈family i ∧
        G≤spanningRestriction P (Sum.elim (fun j=>(Y j).image e) (fun k=>S k∪U k) i) ∧
        (∀ w,G.degree w≤2) ∧ Disjoint G H:=by
    cases i with
    | inl j=>
      obtain ⟨D,hD,hd,hZ⟩:=ho j (H.comap e) (fun v=>
        (Nat.cast_le.mpr (graph_comap_degree_le H e v)).trans (by simpa using hdeg (e v)))
      refine ⟨_,⟨D,hD,rfl,hZ⟩,?_⟩
      simpa only [Sum.elim_inl,←SimpleGraph.ncard_neighborSet] using
        mapped_local_factor_choice Q F P H e (T j) (Y j) r hQ D hD hd
    | inr k=>
      obtain ⟨E,hE,hZ⟩:=he k H (by simpa using hdeg)
      exact ⟨E.graph,⟨E,rfl,hZ⟩,E.graph_le,E.graph_degree,hE⟩
  obtain ⟨G,hG,hdis,hdeg⟩:=hN W (J⊕K) hn 2 P
    (Sum.elim (fun j=>(Y j).image e) (fun k=>S k∪U k)) family hinter hmem hchoice
  have ho' (j:J):∃ D:Finset (LocalOrdinaryCycle Q F (T j) r),
      ((∀ C∈D,∀ E∈D,C≠E→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices E)) ∧
        D.biUnion localOrdinaryVertices=Y j) ∧ (localOrdinaryFactorGraph D).map e=G (Sum.inl j) ∧ Disjoint (G (Sum.inl j)) Z:=(hG (Sum.inl j)).1
  have he' (k:K):∃ E:EndpointPairing P B (S k) (U k),E.graph=G (Sum.inr k) ∧ Disjoint (G (Sum.inr k)) Z:=(hG (Sum.inr k)).1
  choose D hD using ho'
  choose E hE using he'
  have heq (i:J⊕K):Sum.elim (fun j=>(localOrdinaryFactorGraph (D j)).map e)
      (fun k=>(E k).graph) i=G i:=by
    cases i with
    | inl j=>exact (hD j).2.1
    | inr k=>exact (hE k).1
  refine ⟨D,E,fun j=>(hD j).1,?_,?_,?_,?_⟩
  · intro i;rw [heq];exact (hG i).2.1
  · intro i j hij;rw [heq,heq];exact hdis i j hij
  · intro i;rw [heq]
    cases i with
    | inl j=>exact (hD j).2.2
    | inr k=>exact (hE k).2
  · intro w
    have hu:(⨆ i,Sum.elim (fun j=>(localOrdinaryFactorGraph (D j)).map e)
        (fun k=>(E k).graph) i)=⨆ i,G i:=iSup_congr heq
    rw [hu];simpa only [Nat.cast_ofNat] using hdeg w

end Oberwolfach
