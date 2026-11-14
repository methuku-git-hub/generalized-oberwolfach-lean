module

public import Oberwolfach.MarkedHostTransformer
public import Oberwolfach.MarkedHostTransformerBudgets
public import Oberwolfach.MarkedPairProfileMonotonicity
public import Oberwolfach.MarkedTransformerGeometry

@[expose] public section

/-! Uniform marked transformer: its size is chosen before the bounded
forbidden sets, separation radius and forbidden-graph degree bound.
Only the final host-order threshold depends on these later parameters. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 50000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_uniform_host_transformer (l:ℕ) (hl:2≤l)
    (ρ σ q₀ β blo bhi:ℝ) (hρ:0<ρ) (hσ:0<σ) (hq₀:0<q₀) (hβ:0<β) (hblo:0<blo) (hbhi:0<bhi):
    ∃ ε:ℝ,0<ε∧∀ r e:ℕ,∃ a₀ b₀:ℕ,∀ f b:ℕ,∀ dF:ℝ,0≤dF→∃ N:ℕ,
    ∀ (V U E K A S:Type) [Fintype V] [Fintype U] [Fintype A] [Fintype S]
      [DecidableEq V] [DecidableEq U] [DecidableEq A] [DecidableEq S],
    N≤Fintype.card V→
    ∀ (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop) (π:Equiv.Perm V),1≤b→
    ∀ (G:MarkedRootPair tail head ktail khead H₀ HK π b (l+4) A S) (W:Finset V),
    (G.R∪G.R').card≤r→Fintype.card A+Fintype.card S≤e→
    MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l (ρ*Fintype.card V) (σ*Fintype.card V)→
    Function.Injective (markedPhysicalEdge tail head ktail khead π)→
    (G.B.card:ℝ)≤ε*Fintype.card V+f→(W.card:ℝ)≤ε*Fintype.card V+f→
    ∀ F:SimpleGraph V,permutationConflictGraph π b≤F→
    (∀ v z,HK v z→¬H₀ v z)→(∀ v,(F.degree v:ℝ)≤dF)→
    MarkedCommonPairCycleProfiles tail head ktail khead H₀ HK π b l q₀ β blo bhi ε→
    ∃ X T,∃ H:Finset U,
      X.card≤a₀∧H.card≤b₀∧(G.R∪G.R')⊆X∧Disjoint (X\(G.R∪G.R')) W∧
      (∀ x∈X\(G.R∪G.R'),∀ y∈G.R∪G.R',¬PermutationClose π b x y)∧
      (∀ x∈X\(G.R∪G.R'),∀ y∈X\(G.R∪G.R'),x≠y→¬PermutationClose π b x y)∧
      IsResourceTransformer (markedWheelPhysicalResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
        (m:=l+4) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=HK)) G.source G.image T∧
      (∀ e∈T,MarkedResourceSupported tail head ktail khead π X e)∧
      (∀ e∈T,¬MarkedOldResource tail head ktail khead π (G.R∪G.R') G.B e)∧
      (∀ v z,Sum.inr (v,z)∈T→z∈H)∧
      ∀ z∈H,z∈G.B→∃ a:S,G.u a=z∨G.u' a=z:=by
  obtain ⟨ε₀,hε₀,hchoose⟩:=marked_host_transformer l hl q₀ β blo bhi hq₀ hβ hblo hbhi
  let ε:=min ε₀ (min (ρ/2) (σ/2))
  have hε:0<ε:=lt_min hε₀ (lt_min (by positivity) (by positivity))
  have he₀:ε≤ε₀:=min_le_left _ _
  have heρ:ε≤ρ/2:=(min_le_right _ _).trans (min_le_left _ _)
  have heσ:ε≤σ/2:=(min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ε,hε,?_⟩
  intro r e
  let M:=e*(l+6)
  let Zmax:=r+2*e*(l+4)
  let Xmax:=Zmax+M*(l+3)+M*(l+4)+2*M*(l+4)
  let Cmax:=2*(M*(l+3)+M*(l+4))+2*M*(l+4)+Zmax+l+5
  obtain ⟨t,ht,hchoose⟩:=hchoose M
  refine ⟨Xmax+M*((l+5)*t),3*M+2*e,?_⟩
  intro f b dF hdF
  let F₀:ℝ:=f+(Xmax:ℝ)*(dF+1)
  have hF₀:0≤F₀:=by dsimp [F₀];positivity
  obtain ⟨N₁,hchoose⟩:=hchoose F₀ dF hF₀ hdF
  obtain ⟨N₂,hN₂,hbudget⟩:=two_linear_exclusion_budgets ρ σ ε
    ((Cmax:ℝ)*(2*b+1)) (2*e+M) hρ hσ heρ heσ (by positivity) (by positivity) f
  refine ⟨max N₁ N₂,?_⟩
  intro V U E K A S _ _ _ _ _ _ _ _ hn tail head ktail khead H₀ HK π hb G W hr he Q hp hB hW F hconf htypes hF Profiles
  obtain ⟨hi,ha,hs,hz⟩:=G.padded_counts_bounded r e hr he
  change G.paddedRimCount≤M at ha
  change G.paddedSpokeCount≤M at hs
  change G.paddedRowBound≤Zmax at hz
  have ha₁:=Nat.mul_le_mul_right (l+3) ha
  have ha₂:=Nat.mul_le_mul_right (l+4) (Nat.mul_le_mul_left 2 ha)
  have hs₁:=Nat.mul_le_mul_right (l+4) hs
  have hx:G.paddedRowBound+G.paddedRimCount*(l+3)+G.paddedSpokeCount*(l+4)+2*G.paddedRimCount*(l+4)≤Xmax:=by
    dsimp only [Xmax];omega
  have hc:2*(G.paddedRimCount*(l+3)+G.paddedSpokeCount*(l+4))+2*G.paddedRimCount*(l+4)+G.paddedRowBound+l+5≤Cmax:=by
    dsimp only [Cmax];omega
  have hh:2*Fintype.card G.Exceptional+G.paddedRimCount≤2*e+M:=by omega
  obtain ⟨hWr,hBh⟩:=hbudget (Fintype.card V) ((le_max_right _ _).trans hn) W.card G.B.card hW hB
  have hrow:(W.card:ℝ)+(2*((G.paddedRimCount:ℝ)*(l+3)+G.paddedSpokeCount*(l+4))+
      2*G.paddedRimCount*(l+4)+G.paddedRowBound+l+5)*(2*b+1)<ρ*Fintype.card V:=by
    have hc':2*((G.paddedRimCount:ℝ)*(l+3)+G.paddedSpokeCount*(l+4))+
        2*G.paddedRimCount*(l+4)+G.paddedRowBound+l+5≤Cmax:=by exact_mod_cast hc
    have hh:=mul_le_mul_of_nonneg_right hc' (show 0≤(2*b+1:ℝ) by positivity)
    linarith only [hh,hWr]
  have hhub:(G.B.card:ℝ)+2*Fintype.card G.Exceptional+G.paddedRimCount<σ*Fintype.card V:=by
    have hh':2*(Fintype.card G.Exceptional:ℝ)+G.paddedRimCount≤2*e+M:=by exact_mod_cast hh
    linarith only [hh',hBh]
  have hnum:(W.card:ℝ)+(G.paddedRowBound+(G.paddedRimCount:ℝ)*(l+3)+G.paddedSpokeCount*(l+4)+
      2*G.paddedRimCount*(l+4))*(dF+1)≤ε₀*Fintype.card V+F₀:=by
    have hx':(G.paddedRowBound:ℝ)+G.paddedRimCount*(l+3)+G.paddedSpokeCount*(l+4)+2*G.paddedRimCount*(l+4)≤Xmax:=by exact_mod_cast hx
    have hh:=mul_le_mul_of_nonneg_right hx' (show 0≤dF+1 by linarith)
    have hen:=mul_le_mul_of_nonneg_right he₀ (Nat.cast_nonneg (Fintype.card V))
    dsimp only [F₀]
    linarith only [hh,hen,hW]
  obtain ⟨X,Y,T,H,hXc,hZX,hXW,hXZ,hXX,hY,hYc,hYY,hYX,hT,hTs,hTo,hHc,hTh,hHold⟩:=hchoose V U E K A S
    ((le_max_left _ _).trans hn) tail head ktail khead H₀ HK π b hb G W (ρ*Fintype.card V) (σ*Fintype.card V)
    hs Q hp hhub hrow F hnum htypes hF (Profiles.mono_error he₀)
  have hsep:=marked_transformer_free_rows_separated X Y (G.R∪G.R') F hZX
    (hY.mono_right Finset.subset_union_right) hconf hXX hXZ hYY hYX
  refine ⟨X∪Y,T,H,?_,?_,hZX.trans Finset.subset_union_left,?_,hsep.1,hsep.2,hT,hTs,hTo,hTh,hHold⟩
  · exact (Finset.card_union_le X Y).trans (Nat.add_le_add (hXc.trans hx) hYc)
  · omega
  · apply Finset.disjoint_left.mpr
    intro v hv hvW
    obtain ⟨hv,hvo⟩:=Finset.mem_sdiff.mp hv
    rcases Finset.mem_union.mp hv with hv|hv
    · exact Finset.disjoint_left.mp hXW (Finset.mem_sdiff.mpr ⟨hv,hvo⟩) hvW
    · exact Finset.disjoint_left.mp hY hv (Finset.mem_union_left _ hvW)

end Oberwolfach
