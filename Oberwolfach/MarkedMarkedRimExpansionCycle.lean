module

public import Oberwolfach.MarkedCanonicalCycleCompletion
public import Oberwolfach.MarkedExclusionBudget
public import Oberwolfach.MarkedExpansionPositions

@[expose] public section

/-! Expand a formal marked arc; the old endpoints may coincide. The two
incoming marked requirements have distinct heads because the new head
avoids every old root. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ} {c ch:ℝ}

theorem marked_marked_rim_expansion_cycle
    (Q:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (hl:2≤l) (W Z:Finset V) (x y:V) (hx:x∈Z) (hy:y∈Z)
    (hbudget:(W.card:ℝ)+(Z.card+l+16)*(2*b+1)<c):
    ∃ C:MarkedCycleTuple tail head ktail khead (l+4) π b,
      markedArcPresent tail head ktail khead true x (C.val 0)∧
      markedArcPresent tail head ktail khead true (C.val (Fin.last (l+4))) y∧
      ∀ i,C.val i∉W∧C.val i∉Z∧∀ z∈Z,¬PermutationClose π b (C.val i) z:=by
  have hm:∀ Z':Finset V,∀ a:ℕ,Z'.card+a≤Z.card+(l+16)→
      (W.card:ℝ)+(Z'.card+a)*(2*b+1)<c:=by
    intro Z' a h;exact marked_exclusion_budget_mono W Z Z' a (l+16) b c h
      (by simpa only [Nat.cast_add,Nat.cast_ofNat,add_assoc] using hbudget)
  obtain ⟨w,hw,hwW,hwZ,hws⟩:=marked_candidate_avoiding (π:=π)
    (Finset.univ.filter (fun w=>markedArcPresent tail head ktail khead true x w∧markedSpokesTo H₀ HK false ∅ w))
    W Z (Q.outgoing true false x ∅ (by simp)) (by simpa using hm Z 0 (by omega))
  have hyw:y≠w:=fun hh=>hwZ (hh ▸ hy)
  have hi₁:=Finset.card_insert_le w Z
  obtain ⟨v,hv,hvW,hvZ,hvs⟩:=marked_candidate_avoiding (π:=π)
    (Finset.univ.filter (fun v=>markedArcPresent tail head ktail khead true v y∧
      markedArcPresent tail head ktail khead true v w∧markedSpokesTo H₀ HK false ∅ v))
    W (insert w Z) (Q.twoIncoming true false y w ∅ hyw (by simp))
    (by simpa using hm (insert w Z) 0 (by omega))
  have hi₂:=Finset.card_insert_le v (insert w Z)
  obtain ⟨s,hs,hsW,hsZ,hss⟩:=marked_candidate_avoiding (π:=π)
    (Finset.univ.filter (fun s=>markedArcPresent tail head ktail khead false w s∧markedSpokesTo H₀ HK false ∅ s))
    W (insert v (insert w Z)) (Q.outgoing false false w ∅ (by simp))
    (by simpa using hm (insert v (insert w Z)) 0 (by omega))
  obtain ⟨p,C,hC,hp0,hpn,hpa,_⟩:=marked_canonical_cycle_completion Q hl ∅ (by simp) W (insert w Z) w s v
    (by simp) (hss v (by simp)) (Finset.mem_filter.mp hs).2.1 (Finset.mem_filter.mp hv).2.2.1
    (by simp) (by simp) (by simp) hsW hvW (fun hh=>hsZ (Finset.mem_insert_of_mem hh)) hvZ
    (fun z hz=>hss z (Finset.mem_insert_of_mem hz)) hvs
    (by simpa only [Nat.cast_add,Nat.cast_ofNat,add_assoc] using hm (insert w Z) (l+5) (by omega))
  refine ⟨C,?_,?_,?_⟩
  · simpa only [hC,Fin.cons_zero] using (Finset.mem_filter.mp hw).2.1
  · have he:Fin.last (l+4)=(Fin.last (l+3)).succ:=rfl
    simpa only [hC,he,Fin.cons_succ,hpn] using (Finset.mem_filter.mp hv).2.1
  · intro i;rw [hC]
    refine Fin.cases ?_ (fun k=>?_) i
    · exact ⟨hwW,hwZ,hws⟩
    · simp only [Fin.cons_succ]
      exact ⟨(hpa k).1,fun hh=>(hpa k).2.1 (Finset.mem_insert_of_mem hh),
        fun z hz=>(hpa k).2.2 z (Finset.mem_insert_of_mem hz)⟩

end Oberwolfach
