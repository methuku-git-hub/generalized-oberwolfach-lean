module

public import Oberwolfach.MarkedDiagramAbsorber
public import Oberwolfach.MarkedHostTransformerBudgets

@[expose] public section

/-! The marked relative absorber constructed from the actual host counts
and fixed common-pair profiles. All five graphs and four transformers are
constructed. The small tolerance precedes the bounded input sizes and the
permutation radius; the absorber size precedes the forbidden allowance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 50000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_relative_host_absorber (l:ℕ) (hl:2≤l)
    (ρ σ q₀ β blo bhi:ℝ) (hρ:0<ρ) (hσ:0<σ) (hq₀:0<q₀) (hβ:0<β) (hblo:0<blo) (hbhi:0<bhi):
    ∃ ε:ℝ,0<ε∧∀ s e:ℕ,∃ a₀ b₀:ℕ,∀ f b:ℕ,∀ dF:ℝ,0≤dF→∃ N:ℕ,
    ∀ (V₀ U₀ V U E K A S:Type) [Fintype V₀] [Fintype U₀] [Fintype V] [Fintype U] [Fintype A] [Fintype S]
      [DecidableEq V₀] [DecidableEq U₀] [DecidableEq V] [DecidableEq U] [DecidableEq A] [DecidableEq S],
    N≤Fintype.card V→Fintype.card V₀+Fintype.card U₀≤s→Fintype.card A+Fintype.card S≤e→
    ∀ (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop) (π:Equiv.Perm V),1≤b→
    ∀ (G:IndexedMarkedGraph V₀ U₀ A S),G.IsBalanced (l+4)→
    ∀ (R:IndexedMarkedHostRealization G tail head ktail khead H₀ HK π b) (W:Finset V) (B:Finset U),
    (∀ u,R.hubs u∈B)→
    MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l (ρ*Fintype.card V) (σ*Fintype.card V)→
    Function.Injective (markedPhysicalEdge tail head ktail khead π)→
    (B.card:ℝ)≤ε*Fintype.card V+f→(W.card:ℝ)≤ε*Fintype.card V+f→
    ∀ F:SimpleGraph V,permutationConflictGraph π b≤F→
    (∀ v z,HK v z→¬H₀ v z)→(∀ v,(F.degree v:ℝ)≤dF)→
    MarkedCommonPairCycleProfiles tail head ktail khead H₀ HK π b l q₀ β blo bhi ε→
    ∃ C:MarkedSupportedEdgeSet tail head ktail khead π U,
      IsResourceAbsorber (fun D:MarkedWheel tail head ktail khead (l+4) π b H₀ HK=>markedWheelPhysicalResources D)
        R.resources C.edges∧C.rows.card≤a₀∧C.hubs.card≤b₀∧
      (∀ v∈C.rows,v∈W∪R.rowSet→v∈R.rowSet)∧(∀ u∈C.hubs,u∈B→u∈R.hubSet)∧
      (∀ e∈C.edges,¬MarkedOldResource tail head ktail khead π (W∪R.rowSet) B e)∧
      (∀ v∈C.rows\R.rowSet,∀ w∈C.rows\R.rowSet,v≠w→¬PermutationClose π b v w)∧
      ∀ v∈C.rows\R.rowSet,∀ w∈R.rowSet,¬PermutationClose π b v w:=by
  obtain ⟨ε₀,hε₀,habs⟩:=marked_diagram_absorber l hl ρ σ q₀ β blo bhi hρ hσ hq₀ hβ hblo hbhi
  let ε:=min ε₀ (min (ρ/2) (σ/2))
  have hε:0<ε:=lt_min hε₀ (lt_min (by positivity) (by positivity))
  have he₀:ε≤ε₀:=min_le_left _ _
  have heρ:ε≤ρ/2:=(min_le_right _ _).trans (min_le_left _ _)
  have heσ:ε≤σ/2:=(min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ε,hε,?_⟩
  intro s e
  let M:=markedDiagramSize l s e
  let e':=e*(2*(l+5)+1)
  obtain ⟨a₀,b₀,habs⟩:=habs M e'
  refine ⟨a₀,b₀,?_⟩
  intro f b dF hdF
  obtain ⟨N₀,habs⟩:=habs f b dF hdF
  obtain ⟨N₁,hN₁,hbudget⟩:=two_linear_exclusion_budgets ρ σ ε
    ((s+6*(M:ℝ)+l+16)*(2*b+1)) (6*M) hρ hσ heρ heσ (by positivity) (by positivity) f
  refine ⟨max N₀ N₁,?_⟩
  intro V₀ U₀ V U E K A S _ _ _ _ _ _ _ _ _ _ _ _ hn hs he tail head ktail khead H₀ HK π hb G hG R W B hRH Q hp hB hW F hconf htypes hF Profiles
  have hn₁:N₁≤Fintype.card V:=(le_max_right _ _).trans hn
  have hpos:0<Fintype.card V:=by have hh:=hN₁.trans hn₁;omega
  haveI:Nonempty V:=Fintype.card_pos_iff.mp hpos
  let v₀:V:=Classical.arbitrary V
  have hRs:R.rowSet.card≤s:=R.rowSet_card.trans (by omega)
  have hsM:s≤M:=by dsimp [M,markedDiagramSize];omega
  have hRM:R.rowSet.card≤M:=hRs.trans hsM
  obtain ⟨hWbudget,hBbudget⟩:=hbudget (Fintype.card V) hn₁ W.card B.card hW hB
  have hrow:(W.card:ℝ)+(R.rowSet.card+6*M+l+16)*(2*b+1)<ρ*Fintype.card V:=by
    have hh:(R.rowSet.card:ℝ)≤s:=by exact_mod_cast hRs
    have hmul:=mul_le_mul_of_nonneg_right (show (R.rowSet.card:ℝ)+6*M+l+16≤s+6*M+l+16 by linarith only [hh])
      (show 0≤(2*b+1:ℝ) by positivity)
    linarith only [hmul,hWbudget]
  obtain ⟨D⟩:=marked_host_diagram Q hl G hG R s e hs he v₀ W R.rowSet B R.row_mem hRH hp hrow hBbudget
  have he':Fintype.card (A⊕((A⊕S)×Fin (l+5)))+Fintype.card (S⊕((A⊕S)×Fin (l+5)))≤e':=by
    simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    dsimp only [e']
    nlinarith [Nat.mul_le_mul_right (l+5) he]
  have hεn:=mul_le_mul_of_nonneg_right he₀ (Nat.cast_nonneg (Fintype.card V))
  exact habs V U E K (A⊕((A⊕S)×Fin (l+5))) (S⊕((A⊕S)×Fin (l+5))) ((le_max_left _ _).trans hn)
    tail head ktail khead H₀ HK π hb R.resources W R.rowSet R.rowSet B R.hubSet hRM (by rfl) he' Q hp
    (by linarith only [hB,hεn]) (by linarith only [hW,hεn]) F hconf htypes hF (Profiles.mono_error he₀) D

end Oberwolfach
