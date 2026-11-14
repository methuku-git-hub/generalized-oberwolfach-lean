module

public import Oberwolfach.MarkedFreshMixedBoundarySelectionAvoidance
public import Oberwolfach.MarkedBoundaryRobustSupportEvent
public import Oberwolfach.MarkedBoundarySelectionSupports
public import Oberwolfach.TwoCommonEvents

@[expose] public section

/-! Joint factors and endpoint assignments with the support hypotheses
proved from the actual boundary sample. The two common events use the
same physical coordinates. All later masks and class choices are quantified
inside their intersection. Earlier used edges are avoided explicitly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_fresh_supported_boundary_selection (m:ℕ) (hm:3<m+1) (β κ bLo B:ℝ)
    (hβ:0<β) (hκ:0<κ) (hbLo:0<bLo) (hB:0≤B) :
    ∃ η ζ:ℝ,0<η ∧ 0<ζ ∧ ∀ (p:ℝ) (hp:0<p) (hp1:p≤1) (q:ℕ),∃ N:ℕ,
    ∀ (V U E K J I:Type) [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
      [Fintype E] [DecidableEq E] [Fintype K] [DecidableEq K]
      [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I],
      N≤Fintype.card V→Fintype.card J≤(Fintype.card V)^2→
    ∀ (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V) (b:ℕ)
      (H₀ HK:V→U→Prop) (u:J↪U) (root:I↪V) (X:Finset V) (Z₀:Finset U),
      (∀ j,u j∉Z₀)→(∀ i,root i∉X)→
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
      1-1/(Fintype.card V:ℝ)^q-1/(Fintype.card (V⊕U):ℝ)^q≤
      (FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1)).probability
        (fun σ=>∀ τ:Sym2 (V⊕U)→Bool,
          (∀ x,((Finset.univ.filter (fun a:DirectedBoundaryEdge
            (markedActiveAuxTail tail ktail H₀ HK) (markedActiveAuxHead head khead H₀ HK) (ordinaryInnerVertices X Z₀)=>
            (markedActiveAuxTail tail ktail H₀ HK a.val=x∨markedActiveAuxHead head khead H₀ HK a.val=x)∧
            σ (markedActivePhysicalCoin tail head ktail khead π H₀ HK a.val)≠
              τ (markedActivePhysicalCoin tail head ktail khead π H₀ HK a.val))).card:ℝ)≤p^2*Fintype.card (V⊕U)/2)→
        ∀ Y:J→Finset V,(∀ j v,v∈Y j→H₀ v (u j)∨HK v (u j))→
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
          4*((14*p)*Real.sqrt (14*p)*Fintype.card (V⊕U))+4*(Nat.ceil (4*((14*p)*Real.sqrt (14*p)*Fintype.card (V⊕U))):ℝ)+δ≤loss→
        (∀ j,Y j⊆markedBoundarySpokeRows H₀ HK X τ (u j))→
        (∀ i,A₀ i∪A₁ i∪(X₀ i∪X₁ i)⊆markedBoundaryRimNeighbours tail head ktail khead π X τ (root i))→
        (∀ i,Y₀ i∪Y₁ i⊆markedBoundarySpokeHubs H₀ HK Z₀ τ (root i))→
        ∃ P:∀ j,MarkedHubFactorOn tail head ktail khead m π b H₀ HK (u j) (Y j),
        ∃ Q:∀ i,MarkedEndpointPairing (A₀ i) (A₁ i) (X₀ i) (X₁ i) (Y₀ i) (Y₁ i) H₀ HK π b,
        let G:J⊕I→SimpleGraph (V⊕U):=Sum.elim (fun j=>(P j).graph) (fun i=>(Q i).graph);
          (∀ i j,i≠j→Disjoint (G i) (G j)) ∧
          (∀ i,Disjoint (G i) Z) ∧
          ∀ z,((⨆ i,G i).degree z:ℝ)≤4*((14*p)*Fintype.card (V⊕U))) := by
  obtain ⟨η,ζ,hη,hζ,hbase⟩:=marked_fresh_mixed_boundary_selection_avoiding m hm β κ bLo B hβ hκ hbLo hB
  refine ⟨η,ζ,hη,hζ,?_⟩
  intro p hp hp1 q
  obtain ⟨Nf,hNf⟩:=hbase p hp hp1 (14*p) (by positivity) q
  obtain ⟨Ns,hNs⟩:=marked_boundary_robust_support_event p hp hp1 q
  refine ⟨max Nf Ns,?_⟩
  intro V U E K J I _ _ _ _ _ _ _ _ _ _ _ _ hn hJ tail head ktail khead π b H₀ HK u root X Z₀
    hu hroot hd hphys hsep hsize hcycles hpaths wt hw herr
  have hsel:=hNf V U E K J I (by omega) hJ tail head ktail khead π b H₀ HK u
    hd hphys hsep hsize hcycles hpaths wt hw herr
  have hn':Ns≤Fintype.card (V⊕U):=by simp only [Fintype.card_sum];omega
  have hsupp:=hNs V U E K hn' tail head ktail khead π H₀ HK X Z₀ hphys
  have hboth:=finiteLaw_two_events_lower _ _ _ _ _ hsel hsupp
  apply hboth.trans
  apply finiteLaw_probability_mono
  intro σ hσ τ hτ Y hY hratio hchange A₀ A₁ X₀ X₁ Y₀ Y₁ hYY hbalA hbalX hmarked
    degree tau lam loss htau hlam Z δ hZ hdegree hmargin hgap hcutloss hloss
    B₁ B₂ B₃ B₄ B₅ hbudget hYS hAS hBS
  obtain ⟨_,hpair,hmem⟩:=hσ.2 τ hτ
  obtain ⟨hpair',hmem'⟩:=marked_boundary_selection_supports tail head ktail khead π H₀ HK X Z₀ τ
    u root hu hroot Y A₀ A₁ X₀ X₁ Y₀ Y₁ hYS hAS hBS _ _ hpair hmem
  exact hσ.1 Y hY hratio hchange A₀ A₁ X₀ X₁ Y₀ Y₁ hYY hbalA hbalX hmarked
    degree tau lam loss htau hlam Z δ hZ hdegree hmargin hgap hcutloss hloss
    B₁ B₂ B₃ B₄ B₅ hbudget hpair' hmem'

end Oberwolfach
