module

public import Oberwolfach.MarkedHubFactorOn
public import Oberwolfach.MarkedEndpointPairingConstruction
public import Oberwolfach.IndexedGraphSelection

@[expose] public section

/-! Simultaneous physical selection avoiding the actual initial deletion graph.
The entire initial degree is charged before any selection. Simultaneous physical selection of marked hub factors and marked row
endpoint assignments. The endpoint choices are constructed from the five
actual degree/cut blocks. The factor input is discharged by the fresh
marked hub theorem in its sampling caller. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem select_mixed_marked_boundary_avoiding (p:ℝ) (hp:0<p):
    ∃ N:ℕ,∀ (V U E K J I:Type) [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
      [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I],N≤Fintype.card (V⊕U)→
    ∀ (tail head:E→V) (ktail khead:K→V) (m b:ℕ) (π:Equiv.Perm V) (H₀ HK:V→U→Prop)
      (u:J→U) (Y:J→Finset V)
      (A₀ A₁ X₀ X₁:I→Finset V) (Y₀ Y₁:I→Finset U),
    (∀ j v z,H₀ v (u j)→HK z (u j)→v≠π z)→
    (∀ i,Disjoint (Y₀ i) (Y₁ i))→
    (∀ i,(A₀ i).card+(A₁ i).card=(Y₀ i).card+(Y₁ i).card)→
    (∀ i,(X₀ i).card+(X₁ i).card=(Y₀ i).card+(Y₁ i).card)→
    (∀ i,(A₁ i).card=(Y₁ i).card)→
    ∀ degree tau lam loss:ℝ,0<tau→0<lam→
    ∀ (Z:SimpleGraph (V⊕U)) (δ:ℝ),(∀ z,(Z.degree z:ℝ)≤δ)→
    2*tau+(2*(2*b+1):ℕ)≤degree→(2*(2*b+1):ℕ)<lam*tau→
    (∀ i,((X₁ i).card:ℝ)+2*tau≤(Y₀ i).card)→loss≤lam*tau→
    (∀ i,BipartiteBlockBounds H₀ (fun a=>a∈A₁ i) (fun y=>y∈Y₁ i) (degree+loss) tau (2*lam))→
    (∀ i,BipartiteBlockBounds H₀ (fun a=>a∈A₀ i) (fun y=>y∈Y₀ i) (degree+loss) tau (2*lam))→
    (∀ i,BipartiteBlockBounds HK (fun a=>a∈X₁ i) (fun y=>y∈Y₀ i) (degree+loss) tau (2*lam))→
    (∀ i,BipartiteBlockBounds H₀ (fun a=>a∈X₀ i) (fun y=>y∈Y₀ i) (degree+loss) tau (2*lam))→
    (∀ i,BipartiteBlockBounds H₀ (fun a=>a∈X₀ i) (fun y=>y∈Y₁ i) (degree+loss) tau (2*lam))→
    4*(p*Real.sqrt p*Fintype.card (V⊕U))+4*(Nat.ceil (4*(p*Real.sqrt p*Fintype.card (V⊕U))):ℝ)+δ≤loss→
    (∀ j,∀ F:SimpleGraph V,(∀ v,(F.degree v:ℝ)≤loss)→
      ∃ P:MarkedHubFactorOn tail head ktail khead m π b H₀ HK (u j) (Y j),Disjoint P.rim F)→
    let S:J⊕I→Finset (V⊕U):=Sum.elim
      (fun j=>(Y j∪(Y j).image π).image Sum.inl)
      (fun i=>ordinaryInnerVertices (A₀ i∪A₁ i∪(X₀ i∪X₁ i)) (Y₀ i∪Y₁ i))
    (∀ i j,i≠j→((S i∩S j).card:ℝ)≤p^2*Fintype.card (V⊕U))→
    (∀ z,((Finset.univ.filter (fun i=>z∈S i)).card:ℝ)≤p*Fintype.card (V⊕U))→
    ∃ P:∀ j,MarkedHubFactorOn tail head ktail khead m π b H₀ HK (u j) (Y j),
    ∃ Q:∀ i,MarkedEndpointPairing (A₀ i) (A₁ i) (X₀ i) (X₁ i) (Y₀ i) (Y₁ i) H₀ HK π b,
    let G:J⊕I→SimpleGraph (V⊕U):=Sum.elim (fun j=>(P j).graph) (fun i=>(Q i).graph);
      (∀ i j,i≠j→Disjoint (G i) (G j)) ∧
      (∀ i,Disjoint (G i) Z) ∧
      ∀ z,((⨆ i,G i).degree z:ℝ)≤4*(p*Fintype.card (V⊕U)) := by
  obtain ⟨N,hN⟩:=bounded_degree_selection_indexed p hp
  refine ⟨N,?_⟩
  intro V U E K J I _ _ _ _ _ _ _ _ hn tail head ktail khead m b π H₀ HK u Y
    A₀ A₁ X₀ X₁ Y₀ Y₁ hsep hY hbalA hbalX hmarked degree tau lam loss htau hlam Z δ hZ
    hdegree hmargin hgap hloss B₁ B₂ B₃ B₄ B₅ hbudget hfactor S hinter hmem
  let family:J⊕I→Set (SimpleGraph (V⊕U)):=Sum.elim
    (fun j G=>∃ P:MarkedHubFactorOn tail head ktail khead m π b H₀ HK (u j) (Y j),P.graph=G∧Disjoint P.graph Z)
    (fun i G=>∃ Q:MarkedEndpointPairing (A₀ i) (A₁ i) (X₀ i) (X₁ i) (Y₀ i) (Y₁ i) H₀ HK π b,Q.graph=G∧Disjoint Q.graph Z)
  have hchoice (i:J⊕I) (F:SimpleGraph (V⊕U)) (_hF:F≤spanningRestriction ⊤ (S i))
      (hdeg:∀ z,(F.degree z:ℝ)≤(4:ℕ)*(p*Real.sqrt p*Fintype.card (V⊕U))+
        (4:ℕ)*(Nat.ceil (4*(p*Real.sqrt p*Fintype.card (V⊕U))):ℝ)):
      ∃ G:SimpleGraph (V⊕U),G∈family i ∧ G≤spanningRestriction ⊤ (S i) ∧
        (∀ z,G.degree z≤4) ∧ Disjoint G F := by
    have hFdeg (z:V⊕U):((F⊔Z).degree z:ℝ)≤loss:=by
      have hh:((F⊔Z).degree z:ℝ)≤(F.degree z:ℝ)+(Z.degree z:ℝ):=by
        exact_mod_cast graph_degree_sup_le F Z z
      exact hh.trans ((add_le_add (hdeg z) (hZ z)).trans (by simpa using hbudget))
    cases i with
    | inl j=>
      obtain ⟨P,hP⟩:=hfactor j ((F⊔Z).comap (Sum.inl:V→V⊕U)) (fun v=>
        (Nat.cast_le.mpr (graph_comap_degree_le (F⊔Z) ⟨Sum.inl,Sum.inl_injective⟩ v)).trans (by convert hFdeg (Sum.inl v) using 1 <;> congr!))
      have hd:=P.graph_disjoint (F⊔Z) hP
      exact ⟨P.graph,⟨P,rfl,hd.mono_right le_sup_right⟩,P.graph_restriction,
        fun z=>(P.graph_degree (hsep j) z).trans (by decide),hd.mono_right le_sup_left⟩
    | inr i=>
      obtain ⟨Q,hQ⟩:=marked_endpoint_pairing_after_physical_deletion (A₀ i) (A₁ i) (X₀ i) (X₁ i)
        (Y₀ i) (Y₁ i) (hY i) H₀ HK π b (hbalA i) (hbalX i) (hmarked i)
        degree tau lam loss htau hlam hdegree hmargin (hgap i) hloss
        (B₁ i) (B₂ i) (B₃ i) (B₄ i) (B₅ i) (F⊔Z) (by intro z;convert hFdeg z using 1 <;> congr!)
      refine ⟨Q.graph,⟨Q,rfl,hQ.mono_right le_sup_right⟩,?_,Q.graph_degree,hQ.mono_right le_sup_left⟩
      intro z w hzw
      exact (spanningRestriction_adj _ _ _ _).mpr ⟨Q.graph.ne_of_adj hzw,Q.graph_support z w hzw⟩
  obtain ⟨G,hG,hdis,hdeg⟩:=hN (V⊕U) (J⊕I) hn 4 ⊤ S family hinter hmem hchoice
  have hP (j:J):∃ P:MarkedHubFactorOn tail head ktail khead m π b H₀ HK (u j) (Y j),P.graph=G (Sum.inl j)∧Disjoint P.graph Z:=(hG (Sum.inl j)).1
  have hQ (i:I):∃ Q:MarkedEndpointPairing (A₀ i) (A₁ i) (X₀ i) (X₁ i) (Y₀ i) (Y₁ i) H₀ HK π b,Q.graph=G (Sum.inr i)∧Disjoint Q.graph Z:=(hG (Sum.inr i)).1
  choose P hP hPZ using hP
  choose Q hQ hQZ using hQ
  have heq (i:J⊕I):Sum.elim (fun j=>(P j).graph) (fun i=>(Q i).graph) i=G i:=by
    cases i with
    | inl j=>exact hP j
    | inr i=>exact hQ i
  refine ⟨P,Q,?_,?_,?_⟩
  · intro i j hij;rw [heq,heq];exact hdis i j hij
  · intro i;cases i with
    | inl j=>exact hPZ j
    | inr i=>exact hQZ i
  · intro z
    have he:(⨆ i,Sum.elim (fun j=>(P j).graph) (fun i=>(Q i).graph) i)=⨆ i,G i:=iSup_congr heq
    rw [he];simpa using hdeg z

end Oberwolfach
