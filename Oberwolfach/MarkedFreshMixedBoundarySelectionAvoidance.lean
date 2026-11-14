module

public import Oberwolfach.MarkedFreshHubCommonEvent
public import Oberwolfach.MarkedMixedBoundarySelectionAvoidance

@[expose] public section

/-! Mixed marked boundary choices avoid the actual graph used earlier.
Its full degree is charged before invoking the fixed-weight common event.
Actual mixed boundary choices from fixed marked-cycle weights and the
five endpoint degree/cut blocks. The single-factor premise of the selection
lemma is proved here, uniformly over every later physical forbidden graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_fresh_mixed_boundary_selection_avoiding (m:ℕ) (hm:3<m+1) (β κ bLo B:ℝ)
    (hβ:0<β) (hκ:0<κ) (hbLo:0<bLo) (hB:0≤B) :
    ∃ η ζ:ℝ,0<η ∧ 0<ζ ∧ ∀ (p:ℝ) (hp:0<p) (hp1:p≤1) (ρ:ℝ) (hρ:0<ρ) (q:ℕ),∃ N:ℕ,
    ∀ (V U E K J I:Type) [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
      [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I],
      N≤Fintype.card V→Fintype.card J≤(Fintype.card V)^2→
    ∀ (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V) (b:ℕ)
      (H₀ HK:V→U→Prop) (u:J→U),
      (∀ j v,¬(H₀ v (u j)∧HK v (u j)))→
      Function.Injective (markedPhysicalEdge tail head ktail khead π)→
      (∀ j v z,H₀ v (u j)→HK z (u j)→v≠π z)→
      (∀ j,κ*Fintype.card V≤((Finset.univ.filter (fun v=>H₀ v (u j)∨HK v (u j))).card:ℝ))→
      (∀ j,β*(Fintype.card V:ℝ)^(m+1)≤Fintype.card (HubMarkedCycle tail head ktail khead m π b H₀ HK (u j)))→
      (∀ j i,∀ v v':V,v≠v'→(if i then HK v (u j) else H₀ v (u j))→(if i then HK v' (u j) else H₀ v' (u j))→
        β*(Fintype.card V:ℝ)^m≤Fintype.card (RootFirstCommonMarkedPath tail head ktail khead m π b H₀ HK i v v' (u j) (u j)))→
      ∀ wt:∀ j,HubMarkedCycle tail head ktail khead m π b H₀ HK (u j)→ℝ,
      (∀ j C,bLo/(Fintype.card V:ℝ)^m≤wt j C ∧ wt j C≤B/(Fintype.card V:ℝ)^m)→
      (∀ j v,H₀ v (u j)∨HK v (u j)→|1-hypergraphWeightedDegree (hubMarkedCycleVertices (u j)) (wt j) v|≤η)→
      1-1/(Fintype.card V:ℝ)^q≤
      (FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1)).probability
        (fun σ=>∀ Y:J→Finset V,(∀ j v,v∈Y j→H₀ v (u j)∨HK v (u j))→
          (∀ j,((Y j).filter (fun v=>H₀ v (u j))).card=m*((Y j).filter (fun v=>HK v (u j))).card)→
          (∀ j,((changed (Y j) ((Finset.univ.filter (fun v=>H₀ v (u j)∨HK v (u j))).filter
            (fun v=>σ s(Sum.inl v,Sum.inr (u j))=true))).card:ℝ)≤ζ*(p*Fintype.card V))→
        ∀ (A₀ A₁ X₀ X₁:I→Finset V) (Y₀ Y₁:I→Finset U),
          (∀ i,Disjoint (Y₀ i) (Y₁ i))→
          (∀ i,(A₀ i).card+(A₁ i).card=(Y₀ i).card+(Y₁ i).card)→
          (∀ i,(X₀ i).card+(X₁ i).card=(Y₀ i).card+(Y₁ i).card)→
          (∀ i,(A₁ i).card=(Y₁ i).card)→
        ∀ degree tau lam loss:ℝ,0<tau→0<lam→
          ∀ (Z:SimpleGraph (V⊕U)) (δ:ℝ),(∀ z,(Z.degree z:ℝ)≤δ)→
          2*tau+(2*(2*b+1):ℕ)≤degree→(2*(2*b+1):ℕ)<lam*tau→
          (∀ i,((X₁ i).card:ℝ)+2*tau≤(Y₀ i).card)→loss≤lam*tau→loss≤ζ*(p*Fintype.card V)→
          (∀ i,BipartiteBlockBounds H₀ (fun a=>a∈A₁ i) (fun y=>y∈Y₁ i) (degree+loss) tau (2*lam))→
          (∀ i,BipartiteBlockBounds H₀ (fun a=>a∈A₀ i) (fun y=>y∈Y₀ i) (degree+loss) tau (2*lam))→
          (∀ i,BipartiteBlockBounds HK (fun a=>a∈X₁ i) (fun y=>y∈Y₀ i) (degree+loss) tau (2*lam))→
          (∀ i,BipartiteBlockBounds H₀ (fun a=>a∈X₀ i) (fun y=>y∈Y₀ i) (degree+loss) tau (2*lam))→
          (∀ i,BipartiteBlockBounds H₀ (fun a=>a∈X₀ i) (fun y=>y∈Y₁ i) (degree+loss) tau (2*lam))→
          4*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))+4*(Nat.ceil (4*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))):ℝ)+δ≤loss→
        let S:J⊕I→Finset (V⊕U):=Sum.elim
          (fun j=>(Y j∪(Y j).image π).image Sum.inl)
          (fun i=>ordinaryInnerVertices (A₀ i∪A₁ i∪(X₀ i∪X₁ i)) (Y₀ i∪Y₁ i));
        (∀ i j,i≠j→((S i∩S j).card:ℝ)≤ρ^2*Fintype.card (V⊕U))→
        (∀ z,((Finset.univ.filter (fun i=>z∈S i)).card:ℝ)≤ρ*Fintype.card (V⊕U))→
        ∃ P:∀ j,MarkedHubFactorOn tail head ktail khead m π b H₀ HK (u j) (Y j),
        ∃ Q:∀ i,MarkedEndpointPairing (A₀ i) (A₁ i) (X₀ i) (X₁ i) (Y₀ i) (Y₁ i) H₀ HK π b,
        let G:J⊕I→SimpleGraph (V⊕U):=Sum.elim (fun j=>(P j).graph) (fun i=>(Q i).graph);
          (∀ i j,i≠j→Disjoint (G i) (G j)) ∧
          (∀ i,Disjoint (G i) Z) ∧
          ∀ z,((⨆ i,G i).degree z:ℝ)≤4*(ρ*Fintype.card (V⊕U))) := by
  obtain ⟨η,ζ,hη,hζ,hbase⟩:=marked_fresh_hub_common_event m hm β κ bLo B hβ hκ hbLo hB
  refine ⟨η,ζ,hη,hζ,?_⟩
  intro p hp hp1 ρ hρ q
  obtain ⟨Nf,hNf⟩:=hbase p hp hp1 q
  obtain ⟨Ns,hNs⟩:=select_mixed_marked_boundary_avoiding ρ hρ
  refine ⟨max Nf Ns,?_⟩
  intro V U E K J I _ _ _ _ _ _ _ _ hn hJ tail head ktail khead π b H₀ HK u
    hd hphys hsep hsize hcycles hpaths wt hw herr
  have hh:=hNf V U E K J (by omega) hJ tail head ktail khead π b H₀ HK u
    hd hphys hsep hsize hcycles hpaths wt hw herr
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ Y hY hratio hchange A₀ A₁ X₀ X₁ Y₀ Y₁ hYY hbalA hbalX hmarked
    degree tau lam loss htau hlam Z δ hZ hdegree hmargin hgap hcutloss hloss
    B₁ B₂ B₃ B₄ B₅ hbudget S hinter hmem
  have hn':Ns≤Fintype.card (V⊕U):=by simp only [Fintype.card_sum];omega
  apply hNs V U E K J I hn' tail head ktail khead m b π H₀ HK u Y
    A₀ A₁ X₀ X₁ Y₀ Y₁ hsep hYY hbalA hbalX hmarked degree tau lam loss htau hlam Z δ hZ
    hdegree hmargin hgap hcutloss B₁ B₂ B₃ B₄ B₅ hbudget _ hinter hmem
  intro j F hF
  obtain ⟨D,hD,hdis,_hdeg,_hedges⟩:=hσ j (Y j) (hY j) (hratio j) (hchange j) F
    (fun v=>(hF v).trans hloss)
  exact ⟨⟨D,hD.1,hD.2⟩,hdis⟩

end Oberwolfach
