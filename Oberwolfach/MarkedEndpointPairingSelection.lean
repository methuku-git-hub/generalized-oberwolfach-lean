module

public import Oberwolfach.MarkedEndpointPairingConstruction
public import Oberwolfach.IndexedGraphSelection

@[expose] public section

/-! Simultaneously construct the marked endpoint assignments from their
five physical degree/cut blocks. The selected physical graphs have maximum
union degree at most four times the prescribed support-density bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem select_marked_endpoint_pairings (p:ℝ) (hp:0<p) :
    ∃ N:ℕ,∀ (V U I:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
      [Fintype I] [DecidableEq I],N≤Fintype.card (V⊕U)→
    ∀ (A₀ A₁ X₀ X₁:I→Finset V) (Y₀ Y₁:I→Finset U)
      (H₀ HK:V→U→Prop) (π:Equiv.Perm V) (b:ℕ),
    (∀ i,Disjoint (Y₀ i) (Y₁ i))→
    (∀ i,(A₀ i).card+(A₁ i).card=(Y₀ i).card+(Y₁ i).card)→
    (∀ i,(X₀ i).card+(X₁ i).card=(Y₀ i).card+(Y₁ i).card)→
    (∀ i,(A₁ i).card=(Y₁ i).card)→
    ∀ (degree tau lam loss:ℝ),0<tau→0<lam→
    2*tau+(2*(2*b+1):ℕ)≤degree→(2*(2*b+1):ℕ)<lam*tau→
    (∀ i,((X₁ i).card:ℝ)+2*tau≤(Y₀ i).card)→loss≤lam*tau→
    (∀ i,BipartiteBlockBounds H₀ (fun a=>a∈A₁ i) (fun y=>y∈Y₁ i) (degree+loss) tau (2*lam))→
    (∀ i,BipartiteBlockBounds H₀ (fun a=>a∈A₀ i) (fun y=>y∈Y₀ i) (degree+loss) tau (2*lam))→
    (∀ i,BipartiteBlockBounds HK (fun a=>a∈X₁ i) (fun y=>y∈Y₀ i) (degree+loss) tau (2*lam))→
    (∀ i,BipartiteBlockBounds H₀ (fun a=>a∈X₀ i) (fun y=>y∈Y₀ i) (degree+loss) tau (2*lam))→
    (∀ i,BipartiteBlockBounds H₀ (fun a=>a∈X₀ i) (fun y=>y∈Y₁ i) (degree+loss) tau (2*lam))→
    4*(p*Real.sqrt p*Fintype.card (V⊕U))+4*(Nat.ceil (4*(p*Real.sqrt p*Fintype.card (V⊕U))):ℝ)≤loss→
    let S:=fun i=>ordinaryInnerVertices (A₀ i∪A₁ i∪(X₀ i∪X₁ i)) (Y₀ i∪Y₁ i)
    (∀ i j,i≠j→((S i∩S j).card:ℝ)≤p^2*Fintype.card (V⊕U))→
    (∀ z,((Finset.univ.filter (fun i=>z∈S i)).card:ℝ)≤p*Fintype.card (V⊕U))→
    ∃ P:∀ i,MarkedEndpointPairing (A₀ i) (A₁ i) (X₀ i) (X₁ i) (Y₀ i) (Y₁ i) H₀ HK π b,
      (∀ i j,i≠j→Disjoint (P i).graph (P j).graph) ∧
      ∀ z,((⨆ i,(P i).graph).degree z:ℝ)≤4*(p*Fintype.card (V⊕U)) := by
  obtain ⟨N,hN⟩:=bounded_degree_selection_indexed p hp
  refine ⟨N,?_⟩
  intro V U I _ _ _ _ _ _ hn A₀ A₁ X₀ X₁ Y₀ Y₁ H₀ HK π b hY hbalA hbalX hmarked
    degree tau lam loss htau hlam hdeg hmargin hgap hcutloss B₁ B₂ B₃ B₄ B₅ hbudget S hinter hmem
  let Q:=ordinaryPhysicalGraph (⊥:SimpleGraph V) (fun v u=>H₀ v u∨HK v u)
  let family:I→Set (SimpleGraph (V⊕U)):=fun i G=>
    ∃ P:MarkedEndpointPairing (A₀ i) (A₁ i) (X₀ i) (X₁ i) (Y₀ i) (Y₁ i) H₀ HK π b,P.graph=G
  have hchoice (i:I) (K:SimpleGraph (V⊕U)) (_hK:K≤spanningRestriction Q (S i))
      (hKdeg:∀ z,(K.degree z:ℝ)≤(4:ℕ)*(p*Real.sqrt p*Fintype.card (V⊕U))+
        (4:ℕ)*(Nat.ceil (4*(p*Real.sqrt p*Fintype.card (V⊕U))):ℝ)) :
      ∃ G:SimpleGraph (V⊕U),G∈family i ∧ G≤spanningRestriction Q (S i) ∧
        (∀ z,G.degree z≤4) ∧ Disjoint G K := by
    obtain ⟨P,hP⟩:=marked_endpoint_pairing_after_physical_deletion (A₀ i) (A₁ i) (X₀ i) (X₁ i)
      (Y₀ i) (Y₁ i) (hY i) H₀ HK π b (hbalA i) (hbalX i) (hmarked i)
      degree tau lam loss htau hlam hdeg hmargin (hgap i) hcutloss
      (B₁ i) (B₂ i) (B₃ i) (B₄ i) (B₅ i) K (fun z=>(hKdeg z).trans (by simpa using hbudget))
    refine ⟨P.graph,⟨P,rfl⟩,?_,P.graph_degree,hP⟩
    intro z w hzw
    exact (spanningRestriction_adj Q (S i) z w).mpr ⟨P.graph_le hzw,P.graph_support z w hzw⟩
  obtain ⟨G,hG,hdis,hGdeg⟩:=hN (V⊕U) I hn 4 Q S family hinter hmem hchoice
  have hrep (i:I):∃ P:MarkedEndpointPairing (A₀ i) (A₁ i) (X₀ i) (X₁ i) (Y₀ i) (Y₁ i) H₀ HK π b,P.graph=G i:=(hG i).1
  choose P hP using hrep
  refine ⟨P,?_,?_⟩
  · intro i j hij;rw [hP,hP];exact hdis i j hij
  · intro z
    have he:(⨆ i,(P i).graph)=⨆ i,G i:=iSup_congr hP
    rw [he]
    simpa using hGdeg z

end Oberwolfach
