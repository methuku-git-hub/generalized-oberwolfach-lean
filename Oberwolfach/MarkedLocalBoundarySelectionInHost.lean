module

public import Oberwolfach.MarkedLocalDomainBoundarySelection
public import Oberwolfach.MarkedHubFactorHostLift

@[expose] public section

/-! The selected factors and endpoint pairings are objects of the actual
ambient boundary host. The lift changes neither physical graphs nor the
common event and its quantifier order. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 22000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_local_boundary_selection_in_host (m:ℕ) (hm:3<m+1) (β κ bLo B:ℝ)
    (hβ:0<β) (hκ:0<κ) (hbLo:0<bLo) (hB:0≤B) :
    ∃ η ζ:ℝ,0<η ∧ 0<ζ ∧ ∀ (p:ℝ) (hp:0<p) (hp1:p≤1) (q:ℕ),∃ N:ℕ,
    ∀ (W V U E K EB KB J I:Type) [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
      [Fintype E] [DecidableEq E] [Fintype K] [DecidableEq K]
      [Fintype EB] [DecidableEq EB] [Fintype KB] [DecidableEq KB]
      [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I],
      N≤Fintype.card W→Fintype.card J≤(Fintype.card W)^2→
    ∀ (f:W↪V) (ρ:Equiv.Perm W) (π:Equiv.Perm V),(∀ x,f (ρ x)=π (f x))→
    ∀ (tail head:E→W) (ktail khead:K→W) (b:ℕ)
      (H₀ HK:W→U→Prop)
      (btail bhead:EB→V) (bktail bkhead:KB→V) (B₀ BK:V→U→Prop) (u:J↪U) (root:I↪V) (X:Finset V) (Z₀:Finset U),
      ∀ (e:E→EB) (k:K→KB),
      (∀ a,btail (e a)=f (tail a))→(∀ a,bhead (e a)=f (head a))→
      (∀ a,bktail (k a)=f (ktail a))→(∀ a,bkhead (k a)=f (khead a))→
      (∀ x u,H₀ x u→B₀ (f x) u)→(∀ x u,HK x u→BK (f x) u)→
      Function.Injective (markedPhysicalEdge btail bhead bktail bkhead π)→
      (∀ j,u j∉Z₀)→(∀ i,root i∉X)→
      (∀ j v,¬(H₀ v (u j)∧HK v (u j)))→
      Function.Injective (markedPhysicalEdge tail head ktail khead ρ)→
      (∀ j v z,H₀ v (u j)→HK z (u j)→v≠ρ z)→
      (∀ j,κ*Fintype.card W≤((Finset.univ.filter (fun v=>H₀ v (u j)∨HK v (u j))).card:ℝ))→
      (∀ j,β*(Fintype.card W:ℝ)^(m+1)≤Fintype.card (HubMarkedCycle tail head ktail khead m ρ b H₀ HK (u j)))→
      (∀ j i,∀ v v':W,v≠v'→(if i then HK v (u j) else H₀ v (u j))→(if i then HK v' (u j) else H₀ v' (u j))→
        β*(Fintype.card W:ℝ)^m≤Fintype.card (RootFirstCommonMarkedPath tail head ktail khead m ρ b H₀ HK i v v' (u j) (u j)))→
      ∀ wt:∀ j,HubMarkedCycle tail head ktail khead m ρ b H₀ HK (u j)→ℝ,
      (∀ j C,bLo/(Fintype.card W:ℝ)^m≤wt j C ∧ wt j C≤B/(Fintype.card W:ℝ)^m)→
      (∀ j v,H₀ v (u j)∨HK v (u j)→|1-hypergraphWeightedDegree (hubMarkedCycleVertices (u j)) (wt j) v|≤η)→
      1-1/(Fintype.card W:ℝ)^q-1/(Fintype.card (V⊕U):ℝ)^q≤
      (FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1)).probability
        (fun σ=>∀ τ:Sym2 (V⊕U)→Bool,
          (∀ x,((Finset.univ.filter (fun a:DirectedBoundaryEdge
            (markedActiveAuxTail btail bktail B₀ BK) (markedActiveAuxHead bhead bkhead B₀ BK) (ordinaryInnerVertices X Z₀)=>
            (markedActiveAuxTail btail bktail B₀ BK a.val=x∨markedActiveAuxHead bhead bkhead B₀ BK a.val=x)∧
            σ (markedActivePhysicalCoin btail bhead bktail bkhead π B₀ BK a.val)≠
              τ (markedActivePhysicalCoin btail bhead bktail bkhead π B₀ BK a.val))).card:ℝ)≤p^2*Fintype.card (V⊕U)/2)→
        ∀ Y:J→Finset W,(∀ j v,v∈Y j→H₀ v (u j)∨HK v (u j))→
          (∀ j,((Y j).filter (fun v=>H₀ v (u j))).card=m*((Y j).filter (fun v=>HK v (u j))).card)→
          (∀ j,((changed (Y j) ((Finset.univ.filter (fun v=>H₀ v (u j)∨HK v (u j))).filter
            (fun v=>σ s(Sum.inl (f v),Sum.inr (u j))=true))).card:ℝ)≤ζ*(p*Fintype.card W))→
        ∀ (A₀ A₁ X₀ X₁:I→Finset V) (Y₀ Y₁:I→Finset U),
          (∀ i,Disjoint (Y₀ i) (Y₁ i))→
          (∀ i,(A₀ i).card+(A₁ i).card=(Y₀ i).card+(Y₁ i).card)→
          (∀ i,(X₀ i).card+(X₁ i).card=(Y₀ i).card+(Y₁ i).card)→
          (∀ i,(A₁ i).card=(Y₁ i).card)→
        ∀ degree tau lam loss:ℝ,0<tau→0<lam→
          ∀ (Z:SimpleGraph (V⊕U)) (δ:ℝ),(∀ z,(Z.degree z:ℝ)≤δ)→
          2*tau+(2*(2*b+1):ℕ)≤degree→(2*(2*b+1):ℕ)<lam*tau→
          (∀ i,((X₁ i).card:ℝ)+2*tau≤(Y₀ i).card)→loss≤lam*tau→loss≤ζ*(p*Fintype.card W)→
          (∀ i,BipartiteBlockBounds (spokeRelationImage f H₀) (fun a=>a∈A₁ i) (fun y=>y∈Y₁ i) (degree+loss) tau (2*lam))→
          (∀ i,BipartiteBlockBounds (spokeRelationImage f H₀) (fun a=>a∈A₀ i) (fun y=>y∈Y₀ i) (degree+loss) tau (2*lam))→
          (∀ i,BipartiteBlockBounds (spokeRelationImage f HK) (fun a=>a∈X₁ i) (fun y=>y∈Y₀ i) (degree+loss) tau (2*lam))→
          (∀ i,BipartiteBlockBounds (spokeRelationImage f H₀) (fun a=>a∈X₀ i) (fun y=>y∈Y₀ i) (degree+loss) tau (2*lam))→
          (∀ i,BipartiteBlockBounds (spokeRelationImage f H₀) (fun a=>a∈X₀ i) (fun y=>y∈Y₁ i) (degree+loss) tau (2*lam))→
          4*((14*p)*Real.sqrt (14*p)*Fintype.card (V⊕U))+4*(Nat.ceil (4*((14*p)*Real.sqrt (14*p)*Fintype.card (V⊕U))):ℝ)+δ≤loss→
        (∀ j,(Y j).image f⊆markedBoundarySpokeRows B₀ BK X τ (u j))→
        (∀ i,A₀ i∪A₁ i∪(X₀ i∪X₁ i)⊆markedBoundaryRimNeighbours btail bhead bktail bkhead π X τ (root i))→
        (∀ i,Y₀ i∪Y₁ i⊆markedBoundarySpokeHubs B₀ BK Z₀ τ (root i))→
        ∃ P:∀ j,MarkedHubFactorOn btail bhead bktail bkhead m π b B₀ BK (u j) ((Y j).image f),
        ∃ Q:∀ i,MarkedEndpointPairing (A₀ i) (A₁ i) (X₀ i) (X₁ i) (Y₀ i) (Y₁ i) B₀ BK π b,
        let G:J⊕I→SimpleGraph (V⊕U):=Sum.elim (fun j=>(P j).graph) (fun i=>(Q i).graph);
          (∀ i j,i≠j→Disjoint (G i) (G j)) ∧
          (∀ i,Disjoint (G i) Z) ∧
          ∀ z,((⨆ i,G i).degree z:ℝ)≤4*((14*p)*Fintype.card (V⊕U))) := by
  obtain ⟨η,ζ,hη,hζ,hbase⟩:=marked_local_domain_boundary_selection m hm β κ bLo B hβ hκ hbLo hB
  refine ⟨η,ζ,hη,hζ,?_⟩
  intro p hp hp1 q
  obtain ⟨N,hN⟩:=hbase p hp hp1 q
  refine ⟨N,?_⟩
  intro W V U E K EB KB J I _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hn hJ
    f ρ π hf tail head ktail khead b H₀ HK btail bhead bktail bkhead B₀ BK u root X Z₀
    e k het heh hkt hkh hH₀ hHK hbphys hu hroot hd hphys hsep hsize hcycles hpaths wt hw herr
  have hevent:=hN W V U E K EB KB J I hn hJ f ρ π hf tail head ktail khead b H₀ HK
    btail bhead bktail bkhead B₀ BK u root X Z₀ hbphys hu hroot hd hphys hsep hsize hcycles hpaths wt hw herr
  have h₀:∀ v u,spokeRelationImage f H₀ v u→B₀ v u:=by
    rintro v u ⟨x,hx,hH⟩;exact hx ▸ hH₀ x u hH
  have hK:∀ v u,spokeRelationImage f HK v u→BK v u:=by
    rintro v u ⟨x,hx,hH⟩;exact hx ▸ hHK x u hH
  apply hevent.trans
  apply finiteLaw_probability_mono
  intro σ hσ τ hτ Y hY hratio hchange A₀ A₁ X₀ X₁ Y₀ Y₁ hYY hbalA hbalX hmarked
    degree tau lam loss htau hlam Z δ hZ hdegree hmargin hgap hcutloss hloss
    B₁ B₂ B₃ B₄ B₅ hbudget hYS hAS hBS
  obtain ⟨P,Q,hdis,havoid,hdeg⟩:=hσ τ hτ Y hY hratio hchange A₀ A₁ X₀ X₁ Y₀ Y₁
    hYY hbalA hbalX hmarked degree tau lam loss htau hlam Z δ hZ hdegree hmargin hgap hcutloss hloss
    B₁ B₂ B₃ B₄ B₅ hbudget hYS hAS hBS
  have hP (j:J):∃ P':MarkedHubFactorOn btail bhead bktail bkhead m π b B₀ BK (u j) ((Y j).image f),
      P'.rim=(P j).rim∧P'.graph=(P j).graph:=
    marked_hub_factor_host_lift (f∘tail) (f∘head) (f∘ktail) (f∘khead) btail bhead bktail bkhead
      e k het heh hkt hkh m b π (spokeRelationImage f H₀) (spokeRelationImage f HK) B₀ BK h₀ hK (u j) _ (P j)
  choose P' hPr hPg using hP
  let Q':=fun i=>(Q i).mono B₀ BK h₀ hK
  have hg (i:J⊕I):Sum.elim (fun j=>(P' j).graph) (fun j=>(Q' j).graph) i=
      Sum.elim (fun j=>(P j).graph) (fun j=>(Q j).graph) i:=by
    cases i with
    | inl j=>exact hPg j
    | inr i=>rfl
  refine ⟨P',Q',?_,?_,?_⟩
  · intro i j hij;rw [hg,hg];exact hdis i j hij
  · intro i;rw [hg];exact havoid i
  · intro v
    rw [iSup_congr hg]
    exact hdeg v

end Oberwolfach
