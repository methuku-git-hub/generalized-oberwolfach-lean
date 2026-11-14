module

public import Oberwolfach.MappedFactorGraph
public import Oberwolfach.IndexedGraphSelectionAvoiding
public import Oberwolfach.EndpointFactorGraphChoice

@[expose] public section

/-! Hub cycle factors and row endpoint triangle factors are selected together
in the physical graph. Their shared rim edges are therefore disjoint as well. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem select_mixed_boundary_factors_avoiding (p:ℝ) (hp:0<p):
    ∃ N:ℕ,∀ (V W J K:Type) [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
      [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K],N≤Fintype.card W→
    ∀ (r:ℕ) (Q F:SimpleGraph V) (P B:SimpleGraph W) (e:V↪W),Q.map e≤P→
    ∀ (T Y:J→Finset V) (S U Z:K→Finset W) (hSU:∀ k,Disjoint (S k) (U k))
      (K₀:SimpleGraph W) (δ:ℝ) (hK₀:∀ w,(K₀.degree w:ℝ)≤δ),
    (∀ i j:J⊕K,i≠j→
      ((Sum.elim (fun j=>(Y j).image e) Z i∩Sum.elim (fun j=>(Y j).image e) Z j).card:ℝ)
        ≤p^2*Fintype.card W)→
    (∀ w,((Finset.univ.filter (fun i:J⊕K=>w∈Sum.elim (fun j=>(Y j).image e) Z i)).card:ℝ)
      ≤p*Fintype.card W)→
    (∀ j,∀ H:SimpleGraph V,
      (∀ v,(H.degree v:ℝ)≤2*(p*Real.sqrt p*Fintype.card W)+
        2*(Nat.ceil (4*(p*Real.sqrt p*Fintype.card W)):ℝ)+δ)→
      ∃ D:Finset (LocalOrdinaryCycle Q F (T j) r),
        ((∀ C∈D,∀ E∈D,C≠E→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices E)) ∧
          D.biUnion localOrdinaryVertices=Y j) ∧ Disjoint (localOrdinaryFactorGraph D) H)→
    (∀ k,∀ H:SimpleGraph W,
      (∀ w,(H.degree w:ℝ)≤2*(p*Real.sqrt p*Fintype.card W)+
        2*(Nat.ceil (4*(p*Real.sqrt p*Fintype.card W)):ℝ)+δ)→
      ∃ D:Finset (EndpointTriangle P B (S k) (U k)),
        ((∀ C∈D,∀ E∈D,C≠E→Disjoint (endpointTriangleVertices C) (endpointTriangleVertices E)) ∧
          D.biUnion endpointTriangleVertices=Z k) ∧
        endpointFactorGraph (hSU k) D≤spanningRestriction P (Z k) ∧
        (∀ w,(endpointFactorGraph (hSU k) D).degree w≤2) ∧ Disjoint (endpointFactorGraph (hSU k) D) H)→
    ∃ D:∀ j,Finset (LocalOrdinaryCycle Q F (T j) r),
    ∃ E:∀ k,Finset (EndpointTriangle P B (S k) (U k)),
      (∀ j,(∀ C∈D j,∀ C'∈D j,C≠C'→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices C')) ∧
        (D j).biUnion localOrdinaryVertices=Y j) ∧
      (∀ k,(∀ C∈E k,∀ C'∈E k,C≠C'→Disjoint (endpointTriangleVertices C) (endpointTriangleVertices C')) ∧
        (E k).biUnion endpointTriangleVertices=Z k) ∧
      let G:J⊕K→SimpleGraph W:=Sum.elim
        (fun j=>(localOrdinaryFactorGraph (D j)).map e) (fun k=>endpointFactorGraph (hSU k) (E k))
      (∀ i,G i≤spanningRestriction P (Sum.elim (fun j=>(Y j).image e) Z i)) ∧
      (∀ i j,i≠j→Disjoint (G i) (G j)) ∧
      (∀ i,Disjoint (G i) K₀) ∧
      ∀ w,((⨆ i,G i).degree w:ℝ)≤2*(p*Fintype.card W):=by
  obtain ⟨N,hN⟩:=bounded_degree_selection_indexed_avoiding p hp
  refine ⟨N,?_⟩
  intro V W J K _ _ _ _ _ _ _ _ hn r Q F P B e hQ T Y S U Z hSU K₀ δ hK₀ hinter hmem ho he
  let family:J⊕K→Set (SimpleGraph W):=Sum.elim
    (fun j G=>∃ D:Finset (LocalOrdinaryCycle Q F (T j) r),
      ((∀ C∈D,∀ E∈D,C≠E→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices E)) ∧
        D.biUnion localOrdinaryVertices=Y j) ∧ (localOrdinaryFactorGraph D).map e=G)
    (fun k G=>∃ D:Finset (EndpointTriangle P B (S k) (U k)),
      ((∀ C∈D,∀ E∈D,C≠E→Disjoint (endpointTriangleVertices C) (endpointTriangleVertices E)) ∧
        D.biUnion endpointTriangleVertices=Z k) ∧ endpointFactorGraph (hSU k) D=G)
  have hchoice (i:J⊕K) (H:SimpleGraph W)
      (_hH:H≤spanningRestriction P (Sum.elim (fun j=>(Y j).image e) Z i))
      (hdeg:∀ w,(H.degree w:ℝ)≤(2:ℕ)*(p*Real.sqrt p*Fintype.card W)+
        (2:ℕ)*(Nat.ceil (4*(p*Real.sqrt p*Fintype.card W)):ℝ)+δ):
      ∃ G:SimpleGraph W,G∈family i ∧
        G≤spanningRestriction P (Sum.elim (fun j=>(Y j).image e) Z i) ∧
        (∀ w,G.degree w≤2) ∧ Disjoint G H:=by
    cases i with
    | inl j=>
      obtain ⟨D,hD,hd⟩:=ho j (H.comap e) (fun v=>
        (Nat.cast_le.mpr (graph_comap_degree_le H e v)).trans (by simpa using hdeg (e v)))
      refine ⟨_,⟨D,hD,rfl⟩,?_⟩
      simpa only [Sum.elim_inl,←SimpleGraph.ncard_neighborSet] using
        mapped_local_factor_choice Q F P H e (T j) (Y j) r hQ D hD hd
    | inr k=>
      obtain ⟨D,hD,hs,hd,hdis⟩:=he k H (by simpa using hdeg)
      exact ⟨_,⟨D,hD,rfl⟩,hs,hd,hdis⟩
  obtain ⟨G,hG,hdis,hdeg⟩:=hN W (J⊕K) hn 2 P K₀ δ (Sum.elim (fun j=>(Y j).image e) Z)
    family hK₀ hinter hmem hchoice
  have ho' (j:J):∃ D:Finset (LocalOrdinaryCycle Q F (T j) r),
      ((∀ C∈D,∀ E∈D,C≠E→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices E)) ∧
        D.biUnion localOrdinaryVertices=Y j) ∧ (localOrdinaryFactorGraph D).map e=G (Sum.inl j):=(hG (Sum.inl j)).1
  have he' (k:K):∃ D:Finset (EndpointTriangle P B (S k) (U k)),
      ((∀ C∈D,∀ E∈D,C≠E→Disjoint (endpointTriangleVertices C) (endpointTriangleVertices E)) ∧
        D.biUnion endpointTriangleVertices=Z k) ∧ endpointFactorGraph (hSU k) D=G (Sum.inr k):=(hG (Sum.inr k)).1
  choose D hD using ho'
  choose E hE using he'
  have heq (i:J⊕K):Sum.elim (fun j=>(localOrdinaryFactorGraph (D j)).map e)
      (fun k=>endpointFactorGraph (hSU k) (E k)) i=G i:=by
    cases i with
    | inl j=>exact (hD j).2
    | inr k=>exact (hE k).2
  refine ⟨D,E,fun j=>(hD j).1,fun k=>(hE k).1,?_,?_,?_,?_⟩
  · intro i;rw [heq];exact (hG i).2.1
  · intro i j hij;rw [heq,heq];exact hdis i j hij
  · intro i;rw [heq];exact (hG i).2.2.2
  · intro w
    have hu:(⨆ i,Sum.elim (fun j=>(localOrdinaryFactorGraph (D j)).map e)
        (fun k=>endpointFactorGraph (hSU k) (E k)) i)=⨆ i,G i:=iSup_congr heq
    rw [hu];simpa only [Nat.cast_ofNat] using hdeg w

end Oberwolfach
