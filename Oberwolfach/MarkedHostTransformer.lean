module

public import Oberwolfach.MarkedRootPairTransformer
public import Oberwolfach.MarkedRootPaddingResources
public import Oberwolfach.MarkedRootPaddingSizes
public import Oberwolfach.MarkedRootPaddingGeometry

@[expose] public section

/-! A transformer for the original, unpadded typed root graphs. Both
padding families, the augmented graph, initial diagram and common-hub
switches are constructed. No transformer or factor existence is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 50000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_host_transformer (l:ℕ) (hl:2≤l)
    (q₀ β blo bhi:ℝ) (hq₀:0<q₀) (hβ:0<β) (hblo:0<blo) (hbhi:0<bhi):
    ∃ ε:ℝ,0<ε∧∀ s:ℕ,∃ t:ℕ,1≤t∧∀ F₀ dF:ℝ,0≤F₀→0≤dF→∃ N:ℕ,
    ∀ (V U E K A S:Type) [Fintype V] [Fintype U] [Fintype A] [Fintype S]
      [DecidableEq V] [DecidableEq U] [DecidableEq A] [DecidableEq S],
    N≤Fintype.card V→
    ∀ (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop) (π:Equiv.Perm V) (b:ℕ),1≤b→
    ∀ (G:MarkedRootPair tail head ktail khead H₀ HK π b (l+4) A S) (W:Finset V) (c ch:ℝ),
    G.paddedSpokeCount≤s→
    MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch→
    Function.Injective (markedPhysicalEdge tail head ktail khead π)→
    (G.B.card:ℝ)+2*Fintype.card G.Exceptional+G.paddedRimCount<ch→
    (W.card:ℝ)+(2*((G.paddedRimCount:ℝ)*(l+3)+G.paddedSpokeCount*(l+4))+
      2*G.paddedRimCount*(l+4)+G.paddedRowBound+l+5)*(2*b+1)<c→
    ∀ F:SimpleGraph V,
    (W.card:ℝ)+(G.paddedRowBound+(G.paddedRimCount:ℝ)*(l+3)+G.paddedSpokeCount*(l+4)+2*G.paddedRimCount*(l+4))*(dF+1)≤ε*Fintype.card V+F₀→
    (∀ v z,HK v z→¬H₀ v z)→(∀ v,(F.degree v:ℝ)≤dF)→
    MarkedCommonPairCycleProfiles tail head ktail khead H₀ HK π b l q₀ β blo bhi ε→
    ∃ X Y T,∃ H:Finset U,
      X.card≤G.paddedRowBound+G.paddedRimCount*(l+3)+G.paddedSpokeCount*(l+4)+2*G.paddedRimCount*(l+4)∧
      (G.R∪G.R')⊆X∧Disjoint (X\(G.R∪G.R')) W∧
      (∀ x∈X\(G.R∪G.R'),∀ y∈G.R∪G.R',¬PermutationClose π b x y)∧
      (∀ x∈X\(G.R∪G.R'),∀ y∈X\(G.R∪G.R'),x≠y→¬PermutationClose π b x y)∧
      Disjoint Y (W∪X)∧Y.card≤s*((l+5)*t)∧
      (∀ x∈Y,∀ y∈Y,¬F.Adj x y)∧(∀ x∈Y,∀ y∈X,¬F.Adj x y)∧
      IsResourceTransformer (markedWheelPhysicalResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
        (m:=l+4) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=HK)) G.source G.image T∧
      (∀ e∈T,MarkedResourceSupported tail head ktail khead π (X∪Y) e)∧
      (∀ e∈T,¬MarkedOldResource tail head ktail khead π (G.R∪G.R') G.B e)∧
      H.card≤2*G.paddedSpokeCount+G.paddedRimCount+2*Fintype.card G.Exceptional∧
      (∀ v z,Sum.inr (v,z)∈T→z∈H)∧
      ∀ z∈H,z∈G.B→∃ a:S,G.u a=z∨G.u' a=z:=by
  obtain ⟨ε,hε,hchoose⟩:=marked_root_pair_transformer l hl q₀ β blo bhi hq₀ hβ hblo hbhi
  refine ⟨ε,hε,?_⟩
  intro s
  obtain ⟨t,ht,hchoose⟩:=hchoose s
  refine ⟨t,ht,?_⟩
  intro F₀ dF hF₀ hdF
  obtain ⟨N,hchoose⟩:=hchoose F₀ dF hF₀ hdF
  refine ⟨N,?_⟩
  intro V U E K A S _ _ _ _ _ _ _ _ hn tail head ktail khead H₀ HK π b hb G W c ch hs Q hp hhbudget hbudget F hnum htypes hF Profiles
  have hm:0<l+4:=by omega
  have hbc:0≤(2*b+1:ℝ):=by positivity
  have hpadb:(W.card:ℝ)+(2*(Fintype.card G.Exceptional:ℝ)*(l+4)+(G.R∪G.R').card+l+5)*(2*b+1)<c:=by
    have hz:(G.paddedRowBound:ℝ)=(G.R∪G.R').card+2*Fintype.card G.Exceptional*(l+4):=by
      simp only [MarkedRootPair.paddedRowBound,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    rw [hz] at hbudget
    have hnonneg:0≤(2*((G.paddedRimCount:ℝ)*(l+3)+G.paddedSpokeCount*(l+4))+2*G.paddedRimCount*(l+4))*(2*b+1):=by positivity
    nlinarith only [hbudget,hnonneg]
  have hpadH:(G.B.card:ℝ)+2*Fintype.card G.Exceptional<ch:=by
    have hnonneg:0≤(G.paddedRimCount:ℝ):=Nat.cast_nonneg _
    linarith only [hhbudget,hnonneg]
  obtain ⟨P⟩:=marked_root_padding_construction l hl G W c ch Q hp hpadb hpadH
  let G':=P.pair hm hp
  have hZ:((G'.R∪G'.R').card:ℝ)≤G.paddedRowBound:=by exact_mod_cast P.row_card hm hp
  have hB:((G'.B).card:ℝ)≤G.B.card+2*Fintype.card G.Exceptional:=by exact_mod_cast P.hub_card hm hp
  have hh':(G'.B.card:ℝ)+Fintype.card (A⊕(G.Exceptional×Fin ((l+4)+1)))<ch:=by
    rw [G.padded_rim_count]
    linarith only [hB,hhbudget]
  have hb':(W.card:ℝ)+(2*((Fintype.card (A⊕(G.Exceptional×Fin ((l+4)+1))):ℝ)*(l+3)+
      Fintype.card (S⊕(G.Exceptional×Fin ((l+4)+1)))*(l+4))+
      2*Fintype.card (A⊕(G.Exceptional×Fin ((l+4)+1)))*(l+4)+(G'.R∪G'.R').card+l+5)*(2*b+1)<c:=by
    rw [G.padded_rim_count,G.padded_spoke_count]
    have hh:=mul_le_mul_of_nonneg_right hZ hbc
    nlinarith only [hh,hbudget]
  have hnum':(W.card:ℝ)+((G'.R∪G'.R').card+
      (Fintype.card (A⊕(G.Exceptional×Fin ((l+4)+1))):ℝ)*(l+3)+
      Fintype.card (S⊕(G.Exceptional×Fin ((l+4)+1)))*(l+4)+
      2*Fintype.card (A⊕(G.Exceptional×Fin ((l+4)+1)))*(l+4))*(dF+1)≤ε*Fintype.card V+F₀:=by
    rw [G.padded_rim_count,G.padded_spoke_count]
    have hh:=mul_le_mul_of_nonneg_right hZ (show 0≤dF+1 by linarith)
    nlinarith only [hh,hnum]
  obtain ⟨X,Y,T,H,hXc,hZX,hXW,hXsep,hXX,hY,hYc,hYY,hYX,hT,hTs,hTo,hHc,hTh,hHold⟩:=hchoose V U E K
    (A⊕(G.Exceptional×Fin ((l+4)+1))) (S⊕(G.Exceptional×Fin ((l+4)+1))) hn
    (by simpa only [G.padded_spoke_count] using hs) tail head ktail khead H₀ HK π b hb G' W c ch Q hp
    (P.no_exceptional hm hp) hh' hb' F hnum' htypes hF Profiles
  have hXc':X.card≤G.paddedRowBound+G.paddedRimCount*(l+3)+G.paddedSpokeCount*(l+4)+2*G.paddedRimCount*(l+4):=by
    rw [G.padded_rim_count,G.padded_spoke_count] at hXc
    have hh:=P.row_card hm hp
    change (G'.R∪G'.R').card≤G.paddedRowBound at hh
    omega
  have hXW':Disjoint (X\(G.R∪G.R')) W:=by
    apply Finset.disjoint_left.mpr
    intro v hv hvW
    obtain ⟨hv,hvold⟩:=Finset.mem_sdiff.mp hv
    by_cases hz:v∈G'.R∪G'.R'
    · exact Finset.disjoint_left.mp (P.new_rows_avoid hm hp) (Finset.mem_sdiff.mpr ⟨hz,hvold⟩) hvW
    · exact Finset.disjoint_left.mp hXW (Finset.mem_sdiff.mpr ⟨hv,hz⟩) hvW
  let T':=T∪pairedPaddingResources P.C false∪pairedPaddingResources P.C true
  let H':=H∪Finset.univ.image P.hub
  have hHc':H'.card≤2*G.paddedSpokeCount+G.paddedRimCount+2*Fintype.card G.Exceptional:=by
    have hc:=Finset.card_union_le H (Finset.univ.image P.hub)
    rw [Finset.card_image_of_injective _ P.hub.injective,Finset.card_univ,Fintype.card_prod,Fintype.card_bool] at hc
    rw [G.padded_rim_count,G.padded_spoke_count] at hHc
    dsimp only [H']
    omega
  have hpadS:∀ j,∀ e∈pairedPaddingResources P.C j,MarkedResourceSupported tail head ktail khead π (X∪Y) e:=by
    intro j e he
    exact marked_resource_support_mono (hZX.trans Finset.subset_union_left) e (P.supported hm hp j e he)
  have hgeometry:=P.extended_rows_separated hm hp X hXsep hXX
  refine ⟨X,Y,T',H',hXc',(P.rows_old_subset hm hp).trans hZX,hXW',hgeometry.1,hgeometry.2,hY,hYc,hYY,hYX,
    P.remove hm hp T hT,?_,?_,hHc',?_,?_⟩
  · intro e he
    rcases Finset.mem_union.mp he with he|he
    · rcases Finset.mem_union.mp he with he|he
      · exact hTs e he
      · exact hpadS false e he
    · exact hpadS true e he
  · intro e he hold
    rcases Finset.mem_union.mp he with he|he
    · rcases Finset.mem_union.mp he with he|he
      · apply hTo e he
        cases e with
        | inl e=>
          obtain ⟨a,ha,hat,hah⟩:=hold
          exact ⟨a,ha,P.rows_old_subset hm hp hat,P.rows_old_subset hm hp hah⟩
        | inr vu=>exact ⟨P.rows_old_subset hm hp hold.1,Finset.mem_union_left _ hold.2⟩
      · exact P.no_old_resource hm hp false e he hold
    · exact P.no_old_resource hm hp true e he hold
  · intro v z he
    rcases Finset.mem_union.mp he with he|he
    · rcases Finset.mem_union.mp he with he|he
      · exact Finset.mem_union_left _ (hTh v z he)
      · exact Finset.mem_union_right _ (P.spoke_hubs false v z he)
    · exact Finset.mem_union_right _ (P.spoke_hubs true v z he)

  · intro z hz hzB
    rcases Finset.mem_union.mp hz with hz|hz
    · obtain ⟨a,ha⟩:=hHold z hz (Finset.mem_union_left _ hzB)
      cases a with
      | inl a=>exact ⟨a,ha⟩
      | inr ik=>
        rcases ha with ha|ha
        · have hh:(P.C (false,ik.1)).2.val=z:=ha
          exact ((P.hubs (false,ik.1)).2 (((P.hubs (false,ik.1)).1.symm.trans hh).symm ▸ hzB)).elim
        · have hh:(P.C (true,ik.1)).2.val=z:=ha
          exact ((P.hubs (true,ik.1)).2 (((P.hubs (true,ik.1)).1.symm.trans hh).symm ▸ hzB)).elim
    · obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hz
      exact ((P.hubs i).2 hzB).elim

end Oberwolfach
