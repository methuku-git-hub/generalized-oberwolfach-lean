module

public import Oberwolfach.MarkedBoundaryTotalInnerLoss
public import Oberwolfach.MarkedMixedSelectionBounds
public import Oberwolfach.MarkedBoundaryUniformFinishParameters

@[expose] public section

/-! Complete the selected boundary after the actual earlier packings.
The earlier approximate packing avoids the inner pair. The subsequent
covering and boundary extension share the prescribed total inner loss. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_mixed_boundary_finish_after_packings (l:ℕ) (hl:2≤l) (β ν:ℝ) (hβ:0<β) (hν:0<ν):
    ∃ p₀:ℝ,0<p₀∧p₀≤1∧∀ p:ℝ,0<p→p≤p₀→∀ b:ℕ,∃ n₀:ℕ,
    ∀ (V U E T J I:Type) [Fintype V] [Fintype U] [Fintype E] [Fintype T] [Fintype J] [Fintype I]
      [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq T] [DecidableEq J] [DecidableEq I],
      n₀≤Fintype.card (V⊕U)→
    ∀ (tail head:E→V) (ktail khead:T→V) (H₀ HK:V→U→Prop) (π:Equiv.Perm V)
    (X:Finset V) (Q:MarkedBoundaryExtensionCounts tail head ktail khead H₀ HK X (β*Fintype.card (V⊕U)))
    (hb:1≤b) (hphys:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hX:∀ x,π x∈X↔x∈X) (root:J↪V) (hrootX:∀ j,root j∉X)
    (A₀ A₁ X₀ X₁:J→Finset V) (Y₀ Y₁:J→Finset U)
    (P:∀ j,MarkedEndpointPairing (A₀ j) (A₁ j) (X₀ j) (X₁ j) (Y₀ j) (Y₁ j) H₀ HK π b)
    (incoming:∀ j,(A₀ j⊕A₁ j)↪E⊕T) (outgoing:∀ j,(X₀ j⊕X₁ j)↪E⊕T)
    (hinhead:∀ j a,Sum.elim head khead (incoming j a)=root j)
    (hintail:∀ j a,Sum.elim tail ktail (incoming j a)=taggedSubsetValue (A₀ j) (A₁ j) a)
    (houttail:∀ j a,Sum.elim tail ktail (outgoing j a)=root j)
    (houthead:∀ j a,Sum.elim head khead (outgoing j a)=taggedSubsetValue (X₀ j) (X₁ j) a)
    (hintype:∀ j a,(incoming j a).isRight=a.isRight)
    (houttype:∀ j a,(outgoing j a).isRight=a.isRight)
    (hAX:∀ j,A₀ j∪A₁ j⊆X) (hXX:∀ j,X₀ j∪X₁ j⊆X)
    (hsepA:∀ j a,a∈A₀ j∪A₁ j→¬PermutationClose π b a (root j))
    (hsepX:∀ j a,a∈X₀ j∪X₁ j→¬PermutationClose π b a (root j))
    (hY₀:∀ j u,u∈Y₀ j→H₀ (root j) u) (hY₁:∀ j u,u∈Y₁ j→HK (root j) u)
    (Z:Finset U) (hYZ:∀ j,Y₀ j∪Y₁ j⊆Z)
    (hub:I↪U) (houtside:∀ j,hub j∉Z) (Y:I→Finset V) (hYX:∀ j,Y j⊆X)
    (F:∀ j,MarkedHubFactorOn tail head ktail khead (l+3) π b H₀ HK (hub j) (Y j))
    (hFsep:∀ j v z,H₀ v (hub j)→HK z (hub j)→v≠π z)
    (hcross:∀ i j:I⊕J,i≠j→Disjoint
      (Sum.elim (fun j=>(F j).graph) (fun j=>(P j).graph) i)
      (Sum.elim (fun j=>(F j).graph) (fun j=>(P j).graph) j))
    (hdegree:∀ w,((⨆ i:I⊕J,Sum.elim (fun j=>(F j).graph) (fun j=>(P j).graph) i).degree w:ℝ)≤
      56*p*Fintype.card (V⊕U))
    (M₀ M₁:Finset (MarkedWheel tail head ktail khead (l+3) π b H₀ HK))
    (hM₀:∀ W∈M₀,∀ W'∈M₀,W≠W'→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources W'))
    (hM₁:∀ W∈M₁,∀ W'∈M₁,W≠W'→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources W'))
    (hM₀₁:Disjoint (M₀.biUnion markedWheelPhysicalResources) (M₁.biUnion markedWheelPhysicalResources))
    (hM₀inner:∀ e∈M₀.biUnion markedWheelPhysicalResources,¬markedInnerResource X Z e)
    (hinM₀:∀ j a,Sum.inl (markedPhysicalEdge tail head ktail khead π (incoming j a))∉M₀.biUnion markedWheelPhysicalResources)
    (houtM₀:∀ j a,Sum.inl (markedPhysicalEdge tail head ktail khead π (outgoing j a))∉M₀.biUnion markedWheelPhysicalResources)
    (hrootM₀:∀ j u,u∈Y₀ j∪Y₁ j→Sum.inr (root j,u)∉M₀.biUnion markedWheelPhysicalResources)
    (hfactorM₀:∀ j x,x∈Y j→Sum.inr (x,hub j)∉M₀.biUnion markedWheelPhysicalResources)
    (D₀:SimpleGraph (V⊕U)) (hD₀eq:D₀=ordinaryPhysicalGraph (markedPackingRimGraph M₁) (markedPackingSpokes M₁)) (δ₀:ℝ) (hδ₀:0≤δ₀) (hD₀:∀ z,(D₀.degree z:ℝ)≤δ₀)
    (hPD₀:∀ j,Disjoint (P j).graph D₀) (hFD₀:∀ i,Disjoint (F i).graph D₀)
    (hrootSpokeD₀:∀ j u,u∈Y₀ j∪Y₁ j→¬D₀.Adj (Sum.inl (root j)) (Sum.inr u))
    (hfactorSpokeD₀:∀ i v,v∈Y i→¬D₀.Adj (Sum.inl v) (Sum.inr (hub i)))
    (hinD₀:∀ j a,Sum.elim
      (fun e=>¬D₀.Adj (Sum.inl (tail e)) (Sum.inl (head e)))
      (fun e=>¬D₀.Adj (Sum.inl (ktail e)) (Sum.inl (π (khead e)))) (incoming j a))
    (houtD₀:∀ j a,Sum.elim
      (fun e=>¬D₀.Adj (Sum.inl (tail e)) (Sum.inl (head e)))
      (fun e=>¬D₀.Adj (Sum.inl (ktail e)) (Sum.inl (π (khead e)))) (outgoing j a))
    (hDsmall:δ₀≤β*Fintype.card (V⊕U)/6) (hDloss:δ₀≤ν*Fintype.card (V⊕U)/2)
    (hroots:∀ v∉X,∃ j,root j=v) (hhubs:∀ u∉Z,∃ i,hub i=u)
    (hinAll:∀ j a,Sum.elim head khead a=root j→
      Sum.inl (markedPhysicalEdge tail head ktail khead π a)∉(M₀∪M₁).biUnion markedWheelPhysicalResources→∃ w,incoming j w=a)
    (houtAll:∀ j a,Sum.elim tail ktail a=root j→
      Sum.inl (markedPhysicalEdge tail head ktail khead π a)∉(M₀∪M₁).biUnion markedWheelPhysicalResources→∃ w,outgoing j w=a)
    (hrowAll:∀ j u,H₀ (root j) u∨HK (root j) u→
      Sum.inr (root j,u)∉(M₀∪M₁).biUnion markedWheelPhysicalResources→u∈Y₀ j∪Y₁ j)
    (hcolAll:∀ i v,H₀ v (hub i)∨HK v (hub i)→
      Sum.inr (v,hub i)∉(M₀∪M₁).biUnion markedWheelPhysicalResources→v∈Y i)
    (hH:∀ v u,¬(H₀ v u∧HK v u))
    (hdiv:MarkedRemainderDivisible tail head ktail khead HK Finset.univ
      (Finset.univ.filter (fun s:V×U=>H₀ s.1 s.2∨HK s.1 s.2)) (l+3)),
    ∃ N:Finset (MarkedWheel tail head ktail khead (l+3) π b H₀ HK),
      Disjoint ((M₀∪M₁).biUnion markedWheelPhysicalResources) (N.biUnion markedWheelPhysicalResources)∧
      (let M:=M₀∪M₁∪N
       (∀ W∈M,∀ W'∈M,W≠W'→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources W'))∧
       (∀ v,((spanningRestriction (markedPackingRimGraph M) X).degree v:ℝ)≤ν*Fintype.card (V⊕U))∧
       (∀ v∈X,((Z.filter (markedPackingSpokes M v)).card:ℝ)≤ν*Fintype.card (V⊕U))∧
       (∀ u∈Z,((X.filter (fun v=>markedPackingSpokes M v u)).card:ℝ)≤ν*Fintype.card (V⊕U))∧
       (let A':=Finset.univ\M.biUnion markedWheelArcs
        let S':=(Finset.univ.filter (fun s:V×U=>H₀ s.1 s.2∨HK s.1 s.2))\M.biUnion markedWheelSpokePairs
        MarkedRemainderDivisible tail head ktail khead HK A' S' (l+3)∧
          (∀ a∈A',Sum.elim tail ktail a∈X∧Sum.elim head khead a∈X)∧
          (∀ s∈S',s.1∈X∧s.2∈Z)∧
          (A'.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S'.image Sum.inr)=
            (Finset.univ.image (fun a:E⊕T=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪
              (Finset.univ.filter (fun s:V×U=>H₀ s.1 s.2∨HK s.1 s.2)).image Sum.inr)\
              M.biUnion markedWheelPhysicalResources)):=by
  obtain ⟨p₀,hp₀,hp₀1,hbase⟩:=marked_boundary_finish_parameters_upto l 57 (β/2) (ν/2) (by norm_num) (by positivity) (by positivity)
  refine ⟨p₀,hp₀,hp₀1,?_⟩
  intro p hp hpp b
  obtain ⟨N,hN⟩:=hbase p hp hpp b
  refine ⟨max N (Nat.ceil (1/p)),?_⟩
  intro V U E T J I _ _ _ _ _ _ _ _ _ _ _ _ hn tail head ktail khead H₀ HK π
    X Q hb hphys hX root hrootX A₀ A₁ X₀ X₁ Y₀ Y₁ P incoming outgoing
    hinhead hintail houttail houthead hintype houttype hAX hXX hsepA hsepX hY₀ hY₁
    Z hYZ hub houtside Y hYX F hFsep hcross hdegree
    M₀ M₁ hM₀ hM₁ hM₀₁ hM₀inner hinM₀ houtM₀ hrootM₀ hfactorM₀
    D₀ hD₀eq δ₀ hδ₀ hD₀ hPD₀ hFD₀ hrootSpokeD₀ hfactorSpokeD₀ hinD₀ houtD₀ hDsmall hDloss
    hroots hhubs hinAll houtAll hrowAll hcolAll hH hdiv
  let n:=Fintype.card (V⊕U)
  let D:=Nat.ceil (56*p*n)
  have hn0:(0:ℝ)≤n:=Nat.cast_nonneg _
  have hscale:1≤p*n:=by
    have he:1/p≤(n:ℝ):=(Nat.le_ceil _).trans (Nat.cast_le.mpr (show Nat.ceil (1/p)≤n by omega))
    have hh:=(div_le_iff₀ hp).mp he
    linarith only [hh]
  have hD:(D:ℝ)≤57*p*n:=by
    have he: (D:ℝ)<56*p*n+1:=Nat.ceil_lt_add_one (by positivity)
    nlinarith only [he,hscale]
  have hdeg:∀ w,(⨆ i:I⊕J,Sum.elim (fun j=>(F j).graph) (fun j=>(P j).graph) i).degree w≤D:=by
    intro w
    exact_mod_cast (hdegree w).trans (Nat.le_ceil (56*p*n))
  obtain ⟨hFcross,hPcross,hFrim,hPdegree,hcount⟩:=marked_mixed_selection_bounds hub Y F
    A₀ A₁ X₀ X₁ Y₀ Y₁ P D hcross hdeg
  have hU:(Fintype.card U:ℝ)≤n:=by
    exact_mod_cast (show Fintype.card U≤n by dsimp [n];simp only [Fintype.card_sum];omega)
  have hcount':(Fintype.card (Σ j,Y₀ j⊕Y₁ j):ℝ)≤57*p*(n:ℝ)^2:=by
    have he:(Fintype.card (Σ j,Y₀ j⊕Y₁ j):ℝ)≤Fintype.card U*(D:ℝ):=by exact_mod_cast hcount
    have h₁:=mul_le_mul_of_nonneg_right hU (Nat.cast_nonneg (α:=ℝ) D)
    have h₂:=mul_le_mul_of_nonneg_left hD hn0
    nlinarith only [he,h₁,h₂]
  obtain ⟨hK,hbudget,hrow,hcol⟩:=hN n (Fintype.card (Σ j,Y₀ j⊕Y₁ j)) D (by omega) D hcount' hD hD
  let K:=Nat.ceil (Real.sqrt p*n)
  have hbudget':(Fintype.card (Σ j,Y₀ j⊕Y₁ j)*(l+4):ℕ)/(K:ℝ)+D+(D*(l+4):ℕ)+
      (l+5)*(2*b+1)+2*((D:ℝ)+4*(K+D:ℕ))<β*n-3*δ₀:=by
    change δ₀≤β*n/6 at hDsmall
    linarith only [hbudget,hDsmall]
  obtain ⟨N',hMN,hRN,hSN,hUN,hrem⟩:=marked_selected_boundary_after_packings
    X Q hl hb hphys hX root hrootX A₀ A₁ X₀ X₁ Y₀ Y₁ P hPcross incoming outgoing
    hinhead hintail houttail houthead hintype houttype hAX hXX hsepA hsepX hY₀ hY₁
    D K hK hPdegree Z hYZ hub houtside Y hYX F hFcross hFsep D (Nat.cast_nonneg _)
    (fun v=>Nat.cast_le.mpr (hFrim v)) M₀ M₁ hM₀ hM₁ hM₀₁ hM₀inner
    hinM₀ houtM₀ hrootM₀ hfactorM₀ D₀ hD₀eq δ₀ hδ₀ hD₀ hPD₀ hFD₀
    hrootSpokeD₀ hfactorSpokeD₀ hinD₀ houtD₀ hbudget'
    hroots hhubs hinAll houtAll hrowAll hcolAll hH hdiv
  have hrN:∀ v,((spanningRestriction (markedPackingRimGraph N') X).degree v:ℝ)≤ν*n/2:=by
    intro v
    have hh:=hRN v
    change (D:ℝ)+(5*(K+D):ℕ)≤(ν/2)*n at hrow
    push_cast at hh hrow
    have hnn:0≤(K:ℝ)+(D:ℝ):=by positivity
    linarith only [hh,hrow,hnn]
  have hsN:∀ v∈X,((Z.filter (markedPackingSpokes N' v)).card:ℝ)≤ν*n/2:=by
    intro v hv
    have hh:(↑((Z.filter (markedPackingSpokes N' v)).card):ℝ)≤(K+D:ℕ):=by exact_mod_cast hSN v hv
    change (D:ℝ)+(5*(K+D):ℕ)≤(ν/2)*n at hrow
    push_cast at hh hrow
    have hk0:0≤(K:ℝ):=Nat.cast_nonneg _
    have hd0:0≤(D:ℝ):=Nat.cast_nonneg _
    linarith only [hh,hrow,hk0,hd0]
  have huN:∀ u∈Z,((Finset.univ.filter (fun v=>markedPackingSpokes N' v u)).card:ℝ)≤ν*n/2:=by
    intro u hu
    have hh:=(Nat.cast_le.mpr (hUN u hu)).trans hcol
    linarith only [hh]
  have hsmallcover:∀ z,((ordinaryPhysicalGraph (markedPackingRimGraph M₁) (markedPackingSpokes M₁)).degree z:ℝ)≤δ₀:=by
    intro z
    rw [←hD₀eq]
    exact hD₀ z
  obtain ⟨htR,htS,htU⟩:=marked_boundary_total_inner_loss M₀ M₁ N' X Z hM₀inner
    δ₀ (ν*n/2) (ν*n/2) (ν*n/2) hsmallcover hrN hsN huN
  refine ⟨N',hMN,hrem.1,?_,?_,?_,hrem.2⟩
  · intro v
    have hh:=htR v
    change δ₀≤ν*n/2 at hDloss
    linarith only [hh,hDloss]
  · intro v hv
    have hh:=htS v hv
    change δ₀≤ν*n/2 at hDloss
    linarith only [hh,hDloss]
  · intro u hu
    have hh:=htU u hu
    change δ₀≤ν*n/2 at hDloss
    linarith only [hh,hDloss]

end Oberwolfach
