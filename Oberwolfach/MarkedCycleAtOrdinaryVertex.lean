module

public import Oberwolfach.MarkedPrefixCycleCompletion
public import Oberwolfach.MarkedExclusionBudget

@[expose] public section

/-! A cycle through a prescribed ordinary vertex in canonical position one.
No separation among the other old roots is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ} {c ch:ℝ}

theorem marked_cycle_at_ordinary_vertex
    (Q:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (hl:2≤l) (P:Finset U) (hP:P.card≤2) (W Z:Finset V) (x:V) (hx:x∈Z)
    (hxP:markedSpokesTo H₀ HK false P x)
    (hbudget:(W.card:ℝ)+(Z.card+l+12)*(2*b+1)<c):
    ∃ C:MarkedCycleTuple tail head ktail khead (l+4) π b,
      C.val 1=x∧
      (∀ i:Fin (l+5),i≠1→C.val i∉W∧C.val i∉Z∧∀ z∈Z,¬PermutationClose π b (C.val i) z)∧
      ∀ u∈P,MarkedHubCompatible H₀ HK C.val u:=by
  have hmono:∀ Z':Finset V,∀ a:ℕ,Z'.card+a≤Z.card+(l+12)→
      (W.card:ℝ)+(Z'.card+a)*(2*b+1)<c:=by
    intro Z' a h;exact marked_exclusion_budget_mono W Z Z' a (l+12) b c h
      (by simpa only [Nat.cast_add,Nat.cast_ofNat,add_assoc] using hbudget)
  obtain ⟨v,hv,hvW,hvZ,hvs⟩:=marked_candidate_avoiding (π:=π)
    (Finset.univ.filter (fun v=>markedArcPresent tail head ktail khead false v x∧markedSpokesTo H₀ HK true P v))
    W Z (Q.incoming false true x P hP) (by simpa using hmono Z 0 (by omega))
  have hi:=Finset.card_insert_le v Z
  obtain ⟨z,hz,hzW,hzZ,hzs⟩:=marked_candidate_avoiding (π:=π)
    (Finset.univ.filter (fun z=>markedArcPresent tail head ktail khead false x z∧markedSpokesTo H₀ HK false P z))
    W (insert v Z) (Q.outgoing false false x P hP) (by simpa using hmono (insert v Z) 0 (by omega))
  have hi':=Finset.card_insert_le z (insert v Z)
  obtain ⟨y,hy,hyW,hyZ,hys⟩:=marked_candidate_avoiding (π:=π)
    (Finset.univ.filter (fun y=>markedArcPresent tail head ktail khead true y v∧markedSpokesTo H₀ HK false P y))
    W (insert z (insert v Z)) (Q.incoming true false v P hP)
    (by simpa using hmono (insert z (insert v Z)) 0 (by omega))
  have hzy:¬PermutationClose π b z y:=fun hh=>hys z (Finset.mem_insert_self _ _) ((permutationClose_symm π b _ _).mp hh)
  obtain ⟨p,C,hC,hp0,hpn,hpa,hCP⟩:=marked_prefix_cycle_completion Q hl P hP W (insert v Z) v x z y
    (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hx) (hvs x hx) hzy
    (Finset.mem_filter.mp hv).2.1 (Finset.mem_filter.mp hz).2.1 (Finset.mem_filter.mp hy).2.1
    (Finset.mem_filter.mp hv).2.2 hxP (Finset.mem_filter.mp hz).2.2 (Finset.mem_filter.mp hy).2.2
    hzW hyW hzZ (fun hh=>hyZ (Finset.mem_insert_of_mem hh)) hzs
    (fun w hw=>hys w (Finset.mem_insert_of_mem hw))
    (by simpa only [Nat.cast_add,Nat.cast_ofNat,add_assoc] using hmono (insert v Z) (l+4) (by omega))
  have hroot:C.val (0:Fin (l+4)).succ=x:=by simp only [hC,Fin.cons_succ,Fin.cons_zero]
  refine ⟨C,hroot,?_,hCP⟩
  intro i;refine Fin.cases ?_ (fun j=>?_) i
  · intro hh;simp only [hC,Fin.cons_zero];exact ⟨hvW,hvZ,hvs⟩
  · refine Fin.cases ?_ (fun k=>?_) j
    · intro hh;exact False.elim (hh rfl)
    · intro hh
      simp only [hC,Fin.cons_succ]
      exact ⟨(hpa k).1,fun h=>(hpa k).2.1 (Finset.mem_insert_of_mem h),
        fun w hw=>(hpa k).2.2 w (Finset.mem_insert_of_mem hw)⟩

end Oberwolfach
