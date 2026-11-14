module

public import Oberwolfach.MarkedSamplePrescribedOriginalHost
public import Oberwolfach.MarkedReservedDeletionBudget
public import Oberwolfach.MarkedSamplePackingAvoidedSets

@[expose] public section

/-! Construct the prescribed correction-star packing. The reserved graphs
are determined by the corrected inner graph. Their deletion budgets and
disjointness from the prescribed edges are proved from these definitions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 40000000
set_option maxRecDepth 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_sample_correction_star_packing
    (l:ℕ) (hl:2≤l) (pstar gamma omega:ℝ)
    (hpstar:0<pstar) (hpstar1:pstar≤1) (hg:0<gamma) (hg1:gamma≤1) (ho:0<omega):
    ∃ beta eps delta eta₀:ℝ,0<beta ∧ 0<eps ∧ 0<delta ∧ 0<eta₀ ∧
    ∀ eta:ℝ,0<eta→eta≤eta₀→∀ d:ℕ,1≤d→∃ N:ℕ,1≤N ∧
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    N≤Fintype.card V→ omega*Fintype.card V≤(Fintype.card U:ℝ)→
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V),
    (∀ x,(1/2+gamma/2)*Fintype.card V≤(P.degree x:ℝ))→
    ∀ (p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color),
    pstar≤p→pstar≤k→(∀ u,pstar≤q u g)→(∀ u,pstar≤s u j)→
    ∀ (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop),
    MarkedRowsWithSpokes P π d (l+12) Finset.univ p k q s g j (eps*Fintype.card V) σ H→
    MarkedIndicesWithSpokes π d (l+12) Finset.univ q s g j (eps*Fintype.card V) σ H→
    ∀ (I T:Finset V) (J W:Finset U),
    (∀ x,π x∈I↔x∈I)→(∀ x,π x∈T↔x∈T)→
    (I.card:ℝ)≤beta*Fintype.card V/10→(J.card:ℝ)≤beta*Fintype.card V/10→
    (I.card:ℝ)≤delta*Fintype.card V→(J.card:ℝ)≤delta*Fintype.card V→
    let E₀:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let E₁:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E₀=>e.val.1
    let head:=fun e:E₀=>e.val.2
    let ktail:=fun e:E₁=>e.val.1
    let khead:=fun e:E₁=>e.val.2
    let S:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2)
    ∀ (DA:Finset (E₀⊕E₁)) (DS₀:Finset (V×U)),
    (DA.card:ℝ)≤eta^2*(Fintype.card V:ℝ)^2→(DS₀.card:ℝ)≤eta^2*(Fintype.card V:ℝ)^2→
    (∀ a∈DA,Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I)→
    (∀ v,((DA.filter (fun a=>v=Sum.elim tail ktail a∨v=Sum.elim head khead a)).card:ℝ)≤eta^2*Fintype.card V)→
    (∀ z∈DS₀,z.1∈I∧z.2∈J∧z∈S)→
    (∀ v,((DS₀.filter (fun z=>v=z.1)).card:ℝ)≤eta^2*Fintype.card V)→
    (∀ u,((DS₀.filter (fun z=>z.2=u)).card:ℝ)≤eta^2*Fintype.card V)→
    let CA:=(Finset.univ.filter (fun a:E₀⊕E₁=>Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I))\DA
    let CS:=(S.filter (fun z=>z.1∈I∧z.2∈J))\DS₀
    let KA:=CA.filter (fun a=>Sum.elim tail ktail a∈T∨Sum.elim head khead a∈T)
    let KS:=CS.filter (fun z=>z.1∈T∨z.2∈W)
    ∃ M:Finset (MarkedWheel tail head ktail khead (l+4) π (3*d) (H false) (H true)),
      (∀ X∈M,∀ Y∈M,X≠Y→Disjoint (markedWheelPhysicalResources X) (markedWheelPhysicalResources Y))∧
      (M.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J)=
        (markedFiniteResources tail head ktail khead π DA DS₀).filter (markedStarResource T W)∧
      (∀ v,((markedPackingRimGraph M).degree v:ℝ)≤24*eta*Fintype.card V)∧
      (∀ v,((Finset.univ.filter (markedPackingSpokes M v)).card:ℝ)≤6*eta*Fintype.card V)∧
      (∀ u,((Finset.univ.filter (fun v=>markedPackingSpokes M v u)).card:ℝ)≤3*(l+5)*eta*Fintype.card V)∧
      M.biUnion markedWheelArcs⊆Finset.univ\KA∧M.biUnion markedWheelSpokePairs⊆S\KS:=by
  obtain ⟨beta,eps,delta,eta₀,hbeta,heps,hdelta,heta₀,hpack⟩:=
    marked_sample_prescribed_packing_avoiding_graphs l hl pstar gamma omega hpstar hpstar1 hg hg1 ho
  refine ⟨beta,eps,delta,eta₀,hbeta,heps,hdelta,heta₀,?_⟩
  intro eta heta hetasmall d hd
  obtain ⟨N,hN,hpack⟩:=hpack eta heta hetasmall d hd
  refine ⟨N,hN,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hU P π hdeg p k q s g j hp hk hq hs σ H hr hi I T J W hI hT hIb hJb hId hJd
  intro E₀ E₁ tail head ktail khead S DA DS₀ hDAcard hDScard hDA hDAdeg hDS hDSrow hDScol CA CS KA KS
  let DR:=markedSampleArcSetGraph P π d σ KA
  let DS:=markedFiniteSpokeGraph KS
  have hKA (a) (ha:a∈KA):Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I:=
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp ha).1).1).2
  have hKS (z) (hz:z∈KS):z.1∈I∧z.2∈J:=
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hz).1).1).2
  have hb:=marked_reserved_packing_deletion_bounds P π d (l+4) σ H I J hI KA KS hKA hKS ∅ 0 0 0
    (by intro x;simp [←SimpleGraph.ncard_neighborSet,markedPackingRimGraph_empty])
    (by intro x;simp [markedPackingSpokes]) (by intro u;simp [markedPackingSpokes])
  simp only [Finset.biUnion_empty,Finset.union_empty,add_zero] at hb
  have hDR (x:V):(DR.degree x:ℝ)≤delta*Fintype.card V:=by simpa only [DR,←SimpleGraph.ncard_neighborSet,Finset.union_empty] using (hb.1 x).trans hId
  have hDSv (x:V):(DS.degree (Sum.inl x):ℝ)≤delta*Fintype.card V:=by simpa only [DS,←SimpleGraph.ncard_neighborSet,Finset.union_empty] using (hb.2.1 x).trans hJd
  have hDSu (u:U):(DS.degree (Sum.inr u):ℝ)≤delta*Fintype.card V:=by simpa only [DS,←SimpleGraph.ncard_neighborSet,Finset.union_empty] using (hb.2.2 u).trans hId
  let EA:=DA.filter (fun a=>Sum.elim tail ktail a∈T∨Sum.elim head khead a∈T)
  let ES:=DS₀.filter (fun z=>z.1∈T∨z.2∈W)
  have hEA:EA⊆DA:=Finset.filter_subset _ _
  have hES:ES⊆DS₀:=Finset.filter_subset _ _
  have havoidA (a) (ha:a∈EA):Sum.elim (fun e=>s(e.val.1,e.val.2)) (fun e=>s(e.val.1,π e.val.2)) a∉DR.edgeFinset:=by
    rw [markedSampleArcSetGraph_coordinate]
    intro hk
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hk).1).2 (hEA ha)
  have havoidS (z) (hz:z∈ES):¬DS.Adj (Sum.inl z.1) (Sum.inr z.2):=by
    rw [markedFiniteSpokeGraph_adj]
    intro hk
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hk).1).2 (hES hz)
  have hAdeg (v:V):((EA.filter (fun a=>v=Sum.elim tail ktail a∨v=Sum.elim head khead a)).card:ℝ)≤eta^2*Fintype.card V:=
    (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset_filter _ hEA))).trans (hDAdeg v)
  have hSrow (v:V):((ES.filter (fun z=>v=z.1)).card:ℝ)≤eta^2*Fintype.card V:=
    (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset_filter _ hES))).trans (hDSrow v)
  have hScol (u:U):((ES.filter (fun z=>z.2=u)).card:ℝ)≤eta^2*Fintype.card V:=
    (Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset_filter _ hES))).trans (hDScol u)
  obtain ⟨M,hM,hinner,hR,hV,hU',havoidR,havoidSp⟩:=hpack V U Γ Color hn hU P π hdeg p k q s g j hp hk hq hs σ H hr hi
    DR DS hDR hDSv hDSu Iᶜ J (by intro x;simp only [Finset.mem_compl,hI])
    (by simpa only [compl_compl] using hIb) hJb EA ES
    ((Nat.cast_le.mpr (Finset.card_le_card hEA)).trans hDAcard)
    ((Nat.cast_le.mpr (Finset.card_le_card hES)).trans hDScard) havoidA
    (fun a ha=>by simpa only [Finset.mem_compl,not_not] using hDA a (hEA ha)) hAdeg
    (fun z hz=>⟨by simpa only [Finset.mem_compl,not_not] using (hDS z (hES hz)).1,
      (hDS z (hES hz)).2.1,(Finset.mem_filter.mp (hDS z (hES hz)).2.2).2⟩)
    havoidS hSrow hScol
  have havoid:=marked_sample_packing_avoids_reserved_sets P π d (l+4) σ H KA KS M havoidR havoidSp
  refine ⟨M,hM,?_,hR,hV,hU',havoid.1,havoid.2⟩
  rw [←markedFiniteResources_star tail head ktail khead π DA DS₀ T W hT]
  convert hinner using 1 <;> congr! <;> simp only [compl_compl]

end Oberwolfach
