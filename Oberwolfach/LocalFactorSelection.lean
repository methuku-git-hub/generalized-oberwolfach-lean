module

public import Oberwolfach.LocalFactorGraphChoice
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

theorem select_local_ordinary_factors (p:ℝ) (hp:0<p):
    ∃ N:ℕ,∀ (V:Type) [Fintype V] [DecidableEq V],N≤Fintype.card V→
    ∀ (L r:ℕ) (Q F:SimpleGraph V) (T Y:Fin L→Finset V),
    (∀ i j,i≠j→((Y i∩Y j).card:ℝ)≤p^2*Fintype.card V)→
    (∀ v,((Finset.univ.filter (fun i=>v∈Y i)).card:ℝ)≤p*Fintype.card V)→
    (∀ i,∀ K:SimpleGraph V,K≤spanningRestriction Q (Y i)→
      (∀ v,(K.degree v:ℝ)≤2*(p*Real.sqrt p*Fintype.card V)+
        2*(Nat.ceil (4*(p*Real.sqrt p*Fintype.card V)):ℝ))→
      ∃ D:Finset (LocalOrdinaryCycle Q F (T i) r),
        ((∀ C∈D,∀ E∈D,C≠E→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices E)) ∧
          D.biUnion localOrdinaryVertices=Y i) ∧
        localOrdinaryFactorGraph D≤spanningRestriction Q (Y i) ∧
        (∀ v,(localOrdinaryFactorGraph D).degree v≤2) ∧ Disjoint (localOrdinaryFactorGraph D) K)→
    ∃ D:∀ i,Finset (LocalOrdinaryCycle Q F (T i) r),
      (∀ i,(∀ C∈D i,∀ E∈D i,C≠E→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices E)) ∧
        (D i).biUnion localOrdinaryVertices=Y i) ∧
      (∀ i j,i≠j→Disjoint (localOrdinaryFactorGraph (D i)) (localOrdinaryFactorGraph (D j))) ∧
      ∀ v,((⨆ i,localOrdinaryFactorGraph (D i)).degree v:ℝ)≤2*(p*Fintype.card V):=by
  obtain ⟨N,hN,hselect⟩:=bounded_degree_selection_from_single_copy p hp
  refine ⟨N,?_⟩
  intro V _ _ hn L r Q F T Y hinter hmem hsingle
  let family:Fin L→Set (SimpleGraph V):=fun i G=>∃ D:Finset (LocalOrdinaryCycle Q F (T i) r),
    ((∀ C∈D,∀ E∈D,C≠E→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices E)) ∧
      D.biUnion localOrdinaryVertices=Y i) ∧ localOrdinaryFactorGraph D=G
  have hchoice (i:Fin L) (K:SimpleGraph V) (hK:K≤spanningRestriction Q (Y i))
      (hdeg:∀ v,(K.degree v:ℝ)≤(2:ℕ)*(p*Real.sqrt p*Fintype.card V)+
        (2:ℕ)*(Nat.ceil (4*(p*Real.sqrt p*Fintype.card V)):ℝ)):
      ∃ G:SimpleGraph V,G∈family i ∧ G≤spanningRestriction Q (Y i) ∧
        (∀ v,G.degree v≤2) ∧ Disjoint G K:=by
    obtain ⟨D,hD,hsub,hdegree,havoid⟩:=hsingle i K hK (by simpa only [Nat.cast_ofNat] using hdeg)
    exact ⟨localOrdinaryFactorGraph D,⟨D,hD,rfl⟩,hsub,hdegree,havoid⟩
  obtain ⟨G,hG,hdis,hdegree⟩:=hselect V hn L 2 Q Y family hinter hmem hchoice
  have hrep (i:Fin L):∃ D:Finset (LocalOrdinaryCycle Q F (T i) r),
      ((∀ C∈D,∀ E∈D,C≠E→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices E)) ∧
        D.biUnion localOrdinaryVertices=Y i) ∧ localOrdinaryFactorGraph D=G i:=(hG i).1
  choose D hD using hrep
  refine ⟨D,fun i=>(hD i).1,?_,?_⟩
  · intro i j hij;rw [(hD i).2,(hD j).2];exact hdis i j hij
  · intro v
    have he:(⨆ i,localOrdinaryFactorGraph (D i))=(⨆ i,G i):=iSup_congr (fun i=>(hD i).2)
    rw [he]
    simpa only [Nat.cast_ofNat] using hdegree v

end Oberwolfach
