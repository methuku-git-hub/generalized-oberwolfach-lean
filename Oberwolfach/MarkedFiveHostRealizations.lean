module

public import Oberwolfach.MarkedAttachmentRealization
public import Oberwolfach.MarkedComparisonAttachment
public import Oberwolfach.MarkedJointExpansionRealizations
public import Oberwolfach.MarkedDiagramModels

@[expose] public section

/-! Construct both attachments and all three expansions of the marked
absorber in one host, with the actual finite exclusion budgets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 36000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V₀ U₀ V U E K A S:Type} [Fintype V₀] [Fintype U₀]
    [Fintype V] [Fintype U] [Fintype A] [Fintype S]
    [DecidableEq V₀] [DecidableEq U₀] [DecidableEq V] [DecidableEq U]
    [DecidableEq A] [DecidableEq S]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ} {c ch:ℝ}

theorem marked_five_host_realizations
    (Q:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (hl:2≤l) (G:IndexedMarkedGraph V₀ U₀ A S) (hG:G.IsBalanced (l+4))
    (R₀:IndexedMarkedHostRealization G tail head ktail khead H₀ HK π b)
    (n e:ℕ) (hn:Fintype.card V₀+Fintype.card U₀≤n) (he:Fintype.card A+Fintype.card S≤e)
    (v₀:V) (W Z:Finset V) (B:Finset U) (hr:∀ v,R₀.rows v∈Z) (hh:∀ u,R₀.hubs u∈B)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hbudget:(W.card:ℝ)+(Z.card+6*markedDiagramSize l n e+l+16)*(2*b+1)<c)
    (hB:(B.card:ℝ)+6*markedDiagramSize l n e<ch):
    ∃ L:IndexedMarkedHostRealization (indexedMarkedExpansion G (l+4) (by omega)) tail head ktail khead H₀ HK π b,
    ∃ extra:Finset (Finset V⊕(V×U)),
      L.resources=R₀.resources∪extra∧Disjoint R₀.resources extra∧
      HasResourceDecomposition (fun C:MarkedWheel tail head ktail khead (l+4) π b H₀ HK=>markedWheelPhysicalResources C) extra∧
      (∀ a∈extra,¬MarkedOldResource tail head ktail khead π Z B a)∧
      (∀ v,L.rows v∈W∪Z→L.rows v∈R₀.rowSet)∧
      (∀ u,L.hubs u∈B→L.hubs u∈R₀.hubSet)∧
    ∃ R:IndexedMarkedHostRealization (indexedMarkedExpansion (indexedMarkedComparison G (l+4) hG) (l+4) (by omega))
        tail head ktail khead H₀ HK π b,
      (∀ u,R.hubs u∉B∪L.hubSet)∧
      (∀ v,R.rows v∉W∧R.rows v∉Z∪L.rowSet∧∀ z∈Z∪L.rowSet,¬PermutationClose π b (R.rows v) z)∧
      HasResourceDecomposition (fun C:MarkedWheel tail head ktail khead (l+4) π b H₀ HK=>markedWheelPhysicalResources C) R.resources∧
    ∃ T:∀ i:Fin 3,IndexedMarkedHostRealization (indexedMarkedExpansion (markedDiagramOldGraph G l hG i) (l+4) (by omega))
        tail head ktail khead H₀ HK π b,
      (∀ i,Function.Injective (T i).rows∧Function.Injective (T i).hubs∧
        (∀ u,(T i).hubs u∉(B∪L.hubSet)∪R.hubSet)∧
        (∀ v,(T i).rows v∉W∧(T i).rows v∉(Z∪L.rowSet)∪R.rowSet∧
          ∀ z∈(Z∪L.rowSet)∪R.rowSet,¬PermutationClose π b ((T i).rows v) z)∧
        PermutationSeparated π b (T i).rows)∧
      ∀ i j,i≠j→Disjoint (T i).rowSet (T j).rowSet∧Disjoint (T i).hubSet (T j).hubSet∧
        ∀ v∈(T i).rowSet,∀ w∈(T j).rowSet,¬PermutationClose π b v w:=by
  let M:=markedDiagramSize l n e
  have hsize:=marked_diagram_model_size G l n e hn he
  have hLv:Fintype.card V₀+Fintype.card (A⊕S)*(l+5)≤M:=by
    simpa only [markedDiagramOldRows,markedDiagramOldRows_fintype,Fin.cases,Fin.induction,Fin.induction.go,Matrix.cons_val_zero] using hsize.1 0
  have hLh:Fintype.card U₀+Fintype.card (A⊕S)≤M:=by
    simpa only [markedDiagramOldHubs,markedDiagramOldHubs_fintype,Fin.cases,Fin.induction,Fin.induction.go,Matrix.cons_val_zero] using hsize.2 0
  have hRv:Fintype.card G.MarkedSpokes*(l+5)+Fintype.card (A⊕S)*(l+5)≤M:=by
    have h:=hsize.1 2
    dsimp [markedDiagramOldRows,markedDiagramOldRows_fintype,Fin.cases,Fin.induction,Fin.induction.go] at h
    simpa only [Fintype.card_prod,Fintype.card_fin] using h
  have hRh:Fintype.card G.MarkedSpokes+Fintype.card (A⊕S)≤M:=by
    have h:=hsize.2 2
    dsimp [markedDiagramOldHubs,markedDiagramOldHubs_fintype,Fin.cases,Fin.induction,Fin.induction.go] at h
    exact h
  have hLi:(Fintype.card (A⊕S):ℝ)*(l+5)≤M:=by exact_mod_cast (show Fintype.card (A⊕S)*(l+5)≤M by omega)
  have hLhi:(Fintype.card (A⊕S):ℝ)≤M:=by exact_mod_cast (show Fintype.card (A⊕S)≤M by omega)
  have hM:0≤(M:ℝ):=by positivity
  have hbpos:0≤(2*b+1:ℝ):=by positivity
  have hleft:(W.card:ℝ)+(Z.card+Fintype.card (A⊕S)*(l+5)+l+12)*(2*b+1)<c:=by
    have hh:=mul_le_mul_of_nonneg_right (show (Z.card:ℝ)+Fintype.card (A⊕S)*(l+5)+l+12≤Z.card+6*M+l+16 by linarith only [hLi,hM]) hbpos
    linarith only [hh,hbudget]
  obtain ⟨L,extra,hpart,hdis,hdec,hav,hold,holdh,hnewh,hnew,hroot⟩:=marked_attachment_realization Q hl G R₀ W Z B hr hh hp hleft
    (by linarith only [hB,hLhi,hM])
  refine ⟨L,extra,hpart,hdis,hdec,hav,?_,?_,?_⟩
  · rintro (v|⟨i,k⟩) hv
    · rw [hold];exact R₀.row_mem v
    · by_cases hk:k=markedAttachmentPosition l G.jr G.js i
      · subst k;rw [hroot];cases i <;> exact R₀.row_mem _
      · rcases Finset.mem_union.mp hv with hv|hv
        · exact ((hnew i k hk).1 hv).elim
        · exact ((hnew i k hk).2.1 hv).elim
  · rintro (u|i) hu
    · rw [holdh];exact R₀.hub_mem u
    · exact (hnewh i hu).elim
  have hLvc:L.rowSet.card≤M:=L.rowSet_card.trans (by simpa only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin] using hLv)
  have hLhc:L.hubSet.card≤M:=L.hubSet_card.trans (by simpa only [Fintype.card_sum] using hLh)
  let Z':=Z∪L.rowSet
  let B':=B∪L.hubSet
  have hzc:(Z'.card:ℝ)≤Z.card+M:=by exact_mod_cast (Finset.card_union_le _ _).trans (Nat.add_le_add_left hLvc _)
  have hbc:(B'.card:ℝ)≤B.card+M:=by exact_mod_cast (Finset.card_union_le _ _).trans (Nat.add_le_add_left hLhc _)
  have hrv:(Fintype.card G.MarkedSpokes:ℝ)*(l+5)+Fintype.card (A⊕S)*(l+5)≤M:=by exact_mod_cast hRv
  have hrh:(Fintype.card G.MarkedSpokes:ℝ)+Fintype.card (A⊕S)≤M:=by exact_mod_cast hRh
  have hright:(W.card:ℝ)+(Z'.card+Fintype.card G.MarkedSpokes*(l+5)+Fintype.card (A⊕S)*(l+5)+l+13)*(2*b+1)<c:=by
    have hh:=mul_le_mul_of_nonneg_right (show (Z'.card:ℝ)+Fintype.card G.MarkedSpokes*(l+5)+Fintype.card (A⊕S)*(l+5)+l+13≤
        Z.card+6*M+l+16 by linarith only [hzc,hrv,hM]) hbpos
    linarith only [hh,hbudget]
  obtain ⟨R,hRhubs,hRrows,hRdec⟩:=marked_comparison_attachment Q hl G hG v₀ W Z' B' hp hright
    (by linarith only [hbc,hrh,hB,hM])
  refine ⟨R,hRhubs,hRrows,hRdec,?_⟩
  have hRvc:R.rowSet.card≤M:=R.rowSet_card.trans (by simpa only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin] using hRv)
  have hRhc:R.hubSet.card≤M:=R.hubSet_card.trans (by simpa only [Fintype.card_sum] using hRh)
  let Z'':=Z'∪R.rowSet
  let B'':=B'∪R.hubSet
  have hzcc:(Z''.card:ℝ)≤Z.card+2*M:=by
    have hi:(Z''.card:ℝ)≤Z'.card+M:=by exact_mod_cast (Finset.card_union_le _ _).trans (Nat.add_le_add_left hRvc _)
    linarith only [hi,hzc]
  have hbcc:(B''.card:ℝ)≤B.card+2*M:=by
    have hi:(B''.card:ℝ)≤B'.card+M:=by exact_mod_cast (Finset.card_union_le _ _).trans (Nat.add_le_add_left hRhc _)
    linarith only [hi,hbc]
  letI (i:Fin 3):DecidableEq (markedDiagramOldRows G l i):=Classical.decEq _
  letI (i:Fin 3):DecidableEq (markedDiagramOldHubs G i):=Classical.decEq _
  apply marked_joint_expansion_realizations Q hl (markedDiagramOldRows G l) (markedDiagramOldHubs G)
    (markedDiagramOldGraph G l hG) M hsize.1 hsize.2 v₀ W Z'' B'' hp
  · simp only [Fintype.card_fin,Nat.cast_ofNat]
    have hh:=mul_le_mul_of_nonneg_right hzcc hbpos
    nlinarith only [hh,hbudget]
  · simp only [Fintype.card_fin,Nat.cast_ofNat]
    linarith only [hbcc,hB]

end Oberwolfach
