module

public import Oberwolfach.MarkedComparisonRealization
public import Oberwolfach.MarkedAttachmentRealization
public import Oberwolfach.IndexedMarkedRealizationGeometry

@[expose] public section

/-! Construct the decomposable endpoint of the marked absorber diagram.
Its comparison wheels and attached wheels are all chosen in the host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V₀ U₀ V U E K A S:Type} [Fintype V₀] [Fintype U₀]
    [Fintype V] [Fintype U] [Fintype A] [Fintype S]
    [DecidableEq V₀] [DecidableEq U₀] [DecidableEq V] [DecidableEq U]
    [DecidableEq A] [DecidableEq S]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ} {c ch:ℝ}

theorem marked_comparison_attachment
    (Q:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (hl:2≤l) (G:IndexedMarkedGraph V₀ U₀ A S) (hG:G.IsBalanced (l+4))
    (v₀:V) (W Z:Finset V) (B:Finset U)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hbudget:(W.card:ℝ)+(Z.card+Fintype.card G.MarkedSpokes*(l+5)+Fintype.card (A⊕S)*(l+5)+l+13)*(2*b+1)<c)
    (hB:(B.card:ℝ)+Fintype.card G.MarkedSpokes+Fintype.card (A⊕S)<ch):
    ∃ T:IndexedMarkedHostRealization (indexedMarkedExpansion (indexedMarkedComparison G (l+4) hG) (l+4) (by omega))
        tail head ktail khead H₀ HK π b,
      (∀ u,T.hubs u∉B)∧
      (∀ v,T.rows v∉W∧T.rows v∉Z∧∀ z∈Z,¬PermutationClose π b (T.rows v) z)∧
      HasResourceDecomposition (fun C:MarkedWheel tail head ktail khead (l+4) π b H₀ HK=>markedWheelPhysicalResources C) T.resources:=by
  have hpos:0≤(Fintype.card (A⊕S):ℝ)*(l+5)*(2*b+1):=by positivity
  obtain ⟨R,hRi,hHi,hRB,hav,hsep,hdec⟩:=marked_comparison_realization Q hl G hG v₀ W Z B hp
    (by nlinarith only [hbudget,hpos]) (by
      have hn:0≤(Fintype.card (A⊕S):ℝ):=by positivity
      linarith only [hB,hn])
  let Z':=Z∪R.rowSet
  let B':=B∪R.hubSet
  have hzc:(Z'.card:ℝ)≤Z.card+Fintype.card G.MarkedSpokes*(l+5):=by
    have hh:Z'.card≤Z.card+Fintype.card (G.MarkedSpokes×Fin (l+5)):=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_left R.rowSet_card _)
    simpa only [Fintype.card_prod,Fintype.card_fin,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using (show (Z'.card:ℝ)≤Z.card+Fintype.card (G.MarkedSpokes×Fin (l+5)) by exact_mod_cast hh)
  have hbc:(B'.card:ℝ)≤B.card+Fintype.card G.MarkedSpokes:=by
    exact_mod_cast (Finset.card_union_le _ _).trans (Nat.add_le_add_left R.hubSet_card _)
  have hrow:(W.card:ℝ)+(Z'.card+Fintype.card (A⊕S)*(l+5)+l+12)*(2*b+1)<c:=by
    have hh:=mul_le_mul_of_nonneg_right (show (Z'.card:ℝ)+Fintype.card (A⊕S)*(l+5)+l+12≤
        Z.card+Fintype.card G.MarkedSpokes*(l+5)+Fintype.card (A⊕S)*(l+5)+l+13 by linarith only [hzc])
      (show 0≤(2*b+1:ℝ) by positivity)
    linarith only [hh,hbudget]
  obtain ⟨T,extra,hT,hdis,hextra,havoid,htold,htoldh,hth,hpriv,hroot⟩:=marked_attachment_realization Q hl
    (indexedMarkedComparison G (l+4) hG) R W Z' B'
    (fun v=>Finset.mem_union_right _ (R.row_mem v)) (fun u=>Finset.mem_union_right _ (R.hub_mem u)) hp hrow
    (by linarith only [hbc,hB])
  refine ⟨T,?_,?_,?_⟩
  · rintro (u|i)
    · rw [htoldh];exact hRB u
    · exact fun hu=>hth i (Finset.mem_union_left _ hu)
  · rintro (v|⟨i,k⟩)
    · rw [htold];exact hav v
    · by_cases hk:k=markedAttachmentPosition l (indexedMarkedComparison G (l+4) hG).jr (indexedMarkedComparison G (l+4) hG).js i
      · subst k;rw [hroot];cases i <;> exact hav _
      · exact ⟨(hpriv i k hk).1,fun hz=>(hpriv i k hk).2.1 (Finset.mem_union_left _ hz),
          fun z hz=>(hpriv i k hk).2.2 z (Finset.mem_union_left _ hz)⟩
  · rw [hT]
    exact resource_decomposition_union _ _ _ hdec hextra hdis

end Oberwolfach
