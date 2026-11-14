module

public import Oberwolfach.MarkedRootPair
public import Oberwolfach.MarkedPaddedHostTransformerFromCounts

@[expose] public section

/-! The padded transformer for a concrete typed root pair. All common
profiles are fixed for ordered distinct hub pairs before the construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 40000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_root_pair_transformer (l:ℕ) (hl:2≤l)
    (q₀ β blo bhi:ℝ) (hq₀:0<q₀) (hβ:0<β) (hblo:0<blo) (hbhi:0<bhi):
    ∃ ε:ℝ,0<ε∧∀ s:ℕ,∃ t:ℕ,1≤t∧∀ F₀ dF:ℝ,0≤F₀→0≤dF→∃ N:ℕ,
    ∀ (V U E K A S:Type) [Fintype V] [Fintype U] [Fintype A] [Fintype S]
      [DecidableEq V] [DecidableEq U] [DecidableEq A] [DecidableEq S],
    N≤Fintype.card V→Fintype.card S≤s→
    ∀ (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop) (π:Equiv.Perm V) (b:ℕ),1≤b→
    ∀ (G:MarkedRootPair tail head ktail khead H₀ HK π b (l+4) A S) (W:Finset V) (c ch:ℝ),
    MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch→
    Function.Injective (markedPhysicalEdge tail head ktail khead π)→
    (∀ v,¬(Fintype.card {e:A // G.dst e=v}=1∧
      (Finset.univ.filter (fun e:{e:A // G.dst e=v}=>G.jr e.val=true)).card=1))→
    G.B.card+Fintype.card A<ch→
    W.card+(2*((Fintype.card A:ℝ)*(l+3)+Fintype.card S*(l+4))+
      2*Fintype.card A*(l+4)+(G.R∪G.R').card+l+5)*(2*b+1)<c→
    ∀ F:SimpleGraph V,
    (W.card:ℝ)+((G.R∪G.R').card+(Fintype.card A:ℝ)*(l+3)+Fintype.card S*(l+4)+2*Fintype.card A*(l+4))*(dF+1)≤ε*Fintype.card V+F₀→
    (∀ v z,HK v z→¬H₀ v z)→(∀ v,(F.degree v:ℝ)≤dF)→
    MarkedCommonPairCycleProfiles tail head ktail khead H₀ HK π b l q₀ β blo bhi ε→
    ∃ X Y T,∃ H:Finset U,
      X.card≤(G.R∪G.R').card+Fintype.card A*(l+3)+Fintype.card S*(l+4)+2*Fintype.card A*(l+4)∧
      (G.R∪G.R')⊆X∧
      Disjoint (X\(G.R∪G.R')) W∧
      (∀ x∈X\(G.R∪G.R'),∀ y∈G.R∪G.R',¬PermutationClose π b x y)∧
      (∀ x∈X\(G.R∪G.R'),∀ y∈X\(G.R∪G.R'),x≠y→¬PermutationClose π b x y)∧
      Disjoint Y (W∪X)∧Y.card≤s*((l+5)*t)∧
      (∀ x∈Y,∀ y∈Y,¬F.Adj x y)∧(∀ x∈Y,∀ y∈X,¬F.Adj x y)∧
      IsResourceTransformer (markedWheelPhysicalResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
        (m:=l+4) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=HK)) G.source G.image T∧
      (∀ e∈T,MarkedResourceSupported tail head ktail khead π (X∪Y) e)∧
      (∀ e∈T,¬MarkedOldResource tail head ktail khead π (G.R∪G.R') G.B e)∧
      H.card≤2*Fintype.card S+Fintype.card A∧
      (∀ v z,Sum.inr (v,z)∈T→z∈H)∧
      ∀ z∈H,z∈G.B→∃ a:S,G.u a=z∨G.u' a=z:=by
  obtain ⟨ε,hε,hchoose⟩:=marked_padded_host_transformer_from_counts l hl q₀ β blo bhi hq₀ hβ hblo hbhi
  refine ⟨ε,hε,?_⟩
  intro s
  obtain ⟨t,ht,hchoose⟩:=hchoose s
  refine ⟨t,ht,?_⟩
  intro F₀ dF hF₀ hdF
  obtain ⟨N,hchoose⟩:=hchoose F₀ dF hF₀ hdF
  refine ⟨N,?_⟩
  intro V U E K A S _ _ _ _ _ _ _ _ hn hs tail head ktail khead H₀ HK π b hb G W c ch Q hp hpad hhbudget hbudget F hnum htypes hF P
  exact hchoose V U E K A S hn hs tail head ktail khead H₀ HK π b hb G.src G.dst G.row G.φ G.u G.u' G.jr G.js W G.R G.R' G.B c ch
    Q hp G.disjointRows G.rimRoots G.spokeRoots G.hubRoots G.sourceArcSeparation G.imageArcSeparation G.fourRootSeparation
    G.rowBalance G.markedRowBalance hpad G.sourceRimInjective G.imageRimInjective G.sourceSpokeInjective G.imageSpokeInjective
    G.rimPresent G.spokePresent hhbudget hbudget G.ψ F G.hubMap G.differentHubs G.filtered_hub_balance hnum htypes hF P

end Oberwolfach
