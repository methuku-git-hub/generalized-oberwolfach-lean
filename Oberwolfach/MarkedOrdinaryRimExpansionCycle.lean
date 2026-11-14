module

public import Oberwolfach.MarkedPrefixCycleCompletion
public import Oberwolfach.MarkedExclusionBudget
public import Oberwolfach.MarkedExpansionPositions

@[expose] public section

/-! Expand a formal ordinary arc x -> y. Its endpoints may coincide. The
new distinguished arc is chosen with both crossed arcs present, then the
remaining wheel is constructed by ordinary path completion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 23000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ} {c ch:ℝ}

theorem marked_ordinary_rim_expansion_cycle
    (Q:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (hl:2≤l) (W Z:Finset V) (x y:V) (hx:x∈Z) (hy:y∈Z)
    (hbudget:(W.card:ℝ)+(Z.card+l+16)*(2*b+1)<c):
    ∃ C:MarkedCycleTuple tail head ktail khead (l+4) π b,
      markedArcPresent tail head ktail khead false x
        (C.val (finRotate (l+5) (markedExpansionRimPosition (l+4) (by omega) false)))∧
      markedArcPresent tail head ktail khead false
        (C.val (markedExpansionRimPosition (l+4) (by omega) false)) y∧
      ∀ i,C.val i∉W∧C.val i∉Z∧∀ z∈Z,¬PermutationClose π b (C.val i) z:=by
  have hm:∀ Z':Finset V,∀ a:ℕ,Z'.card+a≤Z.card+(l+16)→
      (W.card:ℝ)+(Z'.card+a)*(2*b+1)<c:=by
    intro Z' a h;exact marked_exclusion_budget_mono W Z Z' a (l+16) b c h
      (by simpa only [Nat.cast_add,Nat.cast_ofNat,add_assoc] using hbudget)
  obtain ⟨z,hz,hzW,hzZ,hzs⟩:=marked_candidate_avoiding (π:=π)
    (Finset.univ.filter (fun z=>markedArcPresent tail head ktail khead false x z∧markedSpokesTo H₀ HK false ∅ z))
    W Z (Q.outgoing false false x ∅ (by simp)) (by simpa using hm Z 0 (by omega))
  have hyz:y≠z:=fun hh=>hzZ (hh ▸ hy)
  have hi₁:=Finset.card_insert_le z Z
  obtain ⟨v,hv,hvW,hvZ,hvs⟩:=marked_candidate_avoiding (π:=π)
    (Finset.univ.filter (fun v=>markedArcPresent tail head ktail khead false v y∧
      markedArcPresent tail head ktail khead false v z∧markedSpokesTo H₀ HK false ∅ v))
    W (insert z Z) (Q.twoIncoming false false y z ∅ hyz (by simp))
    (by simpa using hm (insert z Z) 0 (by omega))
  have hi₂:=Finset.card_insert_le v (insert z Z)
  obtain ⟨a,ha,haW,haZ,has⟩:=marked_candidate_avoiding (π:=π)
    (Finset.univ.filter (fun a=>markedArcPresent tail head ktail khead false a v∧markedSpokesTo H₀ HK true ∅ a))
    W (insert v (insert z Z)) (Q.incoming false true v ∅ (by simp))
    (by simpa using hm (insert v (insert z Z)) 0 (by omega))
  have hi₃:=Finset.card_insert_le a (insert v (insert z Z))
  obtain ⟨w,hw,hwW,hwZ,hws⟩:=marked_candidate_avoiding (π:=π)
    (Finset.univ.filter (fun w=>markedArcPresent tail head ktail khead true w a∧markedSpokesTo H₀ HK false ∅ w))
    W (insert a (insert v (insert z Z))) (Q.incoming true false a ∅ (by simp))
    (by simpa using hm (insert a (insert v (insert z Z))) 0 (by omega))
  have hsub:insert a (insert v Z)⊆insert a (insert v (insert z Z)):=by intro t ht;simp only [Finset.mem_insert] at ht ⊢;tauto
  have hzsep:∀ t∈insert a (insert v Z),¬PermutationClose π b z t:=by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl|ht
    · exact fun hh=>has z (by simp) ((permutationClose_symm π b _ _).mp hh)
    · rcases Finset.mem_insert.mp ht with rfl|ht
      · exact fun hh=>hvs z (by simp) ((permutationClose_symm π b _ _).mp hh)
      · exact hzs t ht
  have hznot:z∉insert a (insert v Z):=fun hh=>hzsep z hh (Or.inl rfl)
  have hzwd:¬PermutationClose π b z w:=fun hh=>hws z (by simp) ((permutationClose_symm π b _ _).mp hh)
  have hic₁:=Finset.card_insert_le v Z
  have hic₂:=Finset.card_insert_le a (insert v Z)
  obtain ⟨p,C,hC,hp0,hpn,hpa,_⟩:=marked_prefix_cycle_completion Q hl ∅ (by simp) W (insert a (insert v Z)) a v z w
    (by simp) (by simp) (has v (by simp)) hzwd
    (Finset.mem_filter.mp ha).2.1 (Finset.mem_filter.mp hv).2.2.1 (Finset.mem_filter.mp hw).2.1
    (by simp) (by simp) (by simp) (by simp) hzW hwW hznot (fun hh=>hwZ (hsub hh)) hzsep
    (fun t ht=>hws t (hsub ht))
    (by simpa only [Nat.cast_add,Nat.cast_ofNat,add_assoc] using hm (insert a (insert v Z)) (l+4) (by omega))
  have hk:markedExpansionRimPosition (l+4) (by omega) false=(0:Fin (l+4)).succ:=rfl
  have hr:finRotate (l+5) (markedExpansionRimPosition (l+4) (by omega) false)=(0:Fin (l+3)).succ.succ:=by
    change finRotate (l+5) ((0:Fin (l+3)).succ.castSucc)=(0:Fin (l+3)).succ.succ
    exact finRotate_castSucc_eq_succ _ _
  refine ⟨C,?_,?_,?_⟩
  · simpa only [hr,hC,Fin.cons_succ,Fin.cons_zero,hp0] using (Finset.mem_filter.mp hz).2.1
  · simpa only [hk,hC,Fin.cons_succ,Fin.cons_zero] using (Finset.mem_filter.mp hv).2.1
  · intro i;rw [hC]
    refine Fin.cases ?_ (fun j=>?_) i
    · simp only [Fin.cons_zero]
      exact ⟨haW,fun hh=>haZ (by simp [hh]),fun t ht=>has t (by simp [ht])⟩
    · rw [Fin.cons_succ]
      refine Fin.cases ?_ (fun k=>?_) j
      · simp only [Fin.cons_zero]
        exact ⟨hvW,fun hh=>hvZ (by simp [hh]),fun t ht=>hvs t (by simp [ht])⟩
      · simp only [Fin.cons_succ]
        exact ⟨(hpa k).1,fun hh=>(hpa k).2.1 (by simp [hh]),fun t ht=>(hpa k).2.2 t (by simp [ht])⟩

end Oberwolfach
