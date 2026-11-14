module

public import Oberwolfach.MarkedFreshExpansionRealization
public import Oberwolfach.FiniteDependentSeparatedChoices
public import Oberwolfach.IndexedMarkedRealizationGeometry

@[expose] public section

/-! Simultaneous host realisations of finitely many expansions. The
construction proves disjoint rows, distinct hubs, and cross separation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 28000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K A S I:Type} [Fintype V] [Fintype U] [Fintype A] [Fintype S] [Fintype I]
    [DecidableEq V] [DecidableEq U] [DecidableEq A] [DecidableEq S] [DecidableEq I]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ} {c ch:ℝ}

theorem marked_joint_expansion_realizations
    (Q:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (hl:2≤l) (V₀ U₀:I→Type) [∀ i,Fintype (V₀ i)] [∀ i,Fintype (U₀ i)]
    [∀ i,DecidableEq (V₀ i)] [∀ i,DecidableEq (U₀ i)]
    (G:∀ i,IndexedMarkedGraph (V₀ i) (U₀ i) A S)
    (M:ℕ) (hMr:∀ i,Fintype.card (V₀ i)+Fintype.card (A⊕S)*(l+5)≤M)
    (hMh:∀ i,Fintype.card (U₀ i)+Fintype.card (A⊕S)≤M)
    (v₀:V) (W Z:Finset V) (B:Finset U)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hbudget:(W.card:ℝ)+(Z.card+(Fintype.card I+1)*M+l+16)*(2*b+1)<c)
    (hB:(B.card:ℝ)+(Fintype.card I+1)*M<ch):
    ∃ R:∀ i,IndexedMarkedHostRealization (indexedMarkedExpansion (G i) (l+4) (by omega)) tail head ktail khead H₀ HK π b,
      (∀ i,Function.Injective (R i).rows∧Function.Injective (R i).hubs∧
        (∀ u,(R i).hubs u∉B)∧
        (∀ v,(R i).rows v∉W∧(R i).rows v∉Z∧∀ z∈Z,¬PermutationClose π b ((R i).rows v) z)∧
        PermutationSeparated π b (R i).rows)∧
      ∀ i j,i≠j→Disjoint (R i).rowSet (R j).rowSet∧Disjoint (R i).hubSet (R j).hubSet∧
        ∀ v∈(R i).rowSet,∀ w∈(R j).rowSet,¬PermutationClose π b v w:=by
  let C:=fun i=>IndexedMarkedHostRealization (indexedMarkedExpansion (G i) (l+4) (by omega)) tail head ktail khead H₀ HK π b
  let Good:∀ i,C i→Prop:=fun i R=>Function.Injective R.rows∧Function.Injective R.hubs∧
    (∀ v,R.rows v∉W)∧PermutationSeparated π b R.rows
  have hchoose:∀ Z':Finset V,∀ B':Finset U,Z⊆Z'→B⊆B'→
      Z'.card≤Z.card+Fintype.card I*M→B'.card≤B.card+Fintype.card I*M→∀ i:I,
      ∃ R:C i,Good i R∧R.rowSet.card≤M∧R.hubSet.card≤M∧Disjoint R.rowSet Z'∧Disjoint R.hubSet B'∧
        ∀ v∈R.rowSet,∀ w∈Z',¬PermutationClose π b v w:=by
    intro Z' B' hZZ hBB hZc hBc i
    have hzc:(Z'.card:ℝ)≤Z.card+Fintype.card I*M:=by exact_mod_cast hZc
    have hbc:(B'.card:ℝ)≤B.card+Fintype.card I*M:=by exact_mod_cast hBc
    have hmr:(Fintype.card (V₀ i):ℝ)+Fintype.card (A⊕S)*(l+5)≤M:=by exact_mod_cast hMr i
    have hmh:(Fintype.card (U₀ i):ℝ)+Fintype.card (A⊕S)≤M:=by exact_mod_cast hMh i
    have hrow:(W.card:ℝ)+(Z'.card+Fintype.card (V₀ i)+Fintype.card (A⊕S)*(l+5)+l+16)*(2*b+1)<c:=by
      have hh:=mul_le_mul_of_nonneg_right (show (Z'.card:ℝ)+Fintype.card (V₀ i)+Fintype.card (A⊕S)*(l+5)+l+16≤
          Z.card+(Fintype.card I+1)*M+l+16 by nlinarith only [hzc,hmr]) (show 0≤(2*b+1:ℝ) by positivity)
      linarith only [hh,hbudget]
    obtain ⟨R,hRi,hHi,hHB,hav,hsep⟩:=marked_fresh_expansion_realization Q hl (G i) v₀ W Z' B' hp hrow
      (by nlinarith only [hbc,hmh,hB])
    refine ⟨R,⟨hRi,hHi,fun v=>(hav v).1,hsep⟩,?_,?_,?_,?_,?_⟩
    · exact R.rowSet_card.trans (by simpa only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin] using hMr i)
    · exact R.hubSet_card.trans (by simpa only [Fintype.card_sum] using hMh i)
    · apply Finset.disjoint_left.mpr
      intro v hv hz;obtain ⟨x,_,rfl⟩:=Finset.mem_image.mp hv;exact (hav x).2.1 hz
    · apply Finset.disjoint_left.mpr
      intro u hu hb;obtain ⟨x,_,rfl⟩:=Finset.mem_image.mp hu;exact hHB x hb
    · intro v hv z hz;obtain ⟨x,_,rfl⟩:=Finset.mem_image.mp hv;exact (hav x).2.2 z hz
  obtain ⟨R,hR,hd⟩:=finite_dependent_separated_choices C π b (fun _ R=>R.rowSet) (fun _ R=>R.hubSet) Good Z B M M hchoose
  refine ⟨R,?_,hd⟩
  intro i
  refine ⟨(hR i).1.1,(hR i).1.2.1,?_,?_,(hR i).1.2.2.2⟩
  · intro u;exact Finset.disjoint_left.mp (hR i).2.2.2.2.1 ((R i).hub_mem u)
  · intro v
    exact ⟨(hR i).1.2.2.1 v,Finset.disjoint_left.mp (hR i).2.2.2.1 ((R i).row_mem v),
      (hR i).2.2.2.2.2 _ ((R i).row_mem v)⟩

end Oberwolfach
