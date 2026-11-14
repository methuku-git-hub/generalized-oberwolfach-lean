module

public import Oberwolfach.MarkedCycleAtHead

@[expose] public section

/-! An actual canonical marked cycle with every row outside the forbidden
sets. A single supplied ambient vertex is only an anchor for a host count. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ} {c ch:ℝ}

theorem marked_free_cycle
    (Q:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (hl:2≤l) (v₀:V) (W Z:Finset V)
    (hbudget:(W.card:ℝ)+(Z.card+l+13)*(2*b+1)<c):
    ∃ C:MarkedCycleTuple tail head ktail khead (l+4) π b,
      ∀ i,C.val i∉W∧C.val i∉Z∧∀ z∈Z,¬PermutationClose π b (C.val i) z:=by
  have hb:(W.card:ℝ)+Z.card*(2*b+1)<c:=by
    have hh:=marked_exclusion_budget_mono W Z Z 0 (l+13) b c (by omega)
      (by simpa only [Nat.cast_add,Nat.cast_ofNat,add_assoc] using hbudget)
    simpa using hh
  obtain ⟨v,hv,hvW,hvZ,hvs⟩:=marked_candidate_avoiding (π:=π)
    (Finset.univ.filter (fun v=>markedArcPresent tail head ktail khead false v₀ v∧markedSpokesTo H₀ HK false ∅ v))
    W Z (Q.outgoing false false v₀ ∅ (by simp)) hb
  have hi:=Finset.card_insert_le v Z
  have hbc:(W.card:ℝ)+((insert v Z).card+l+12)*(2*b+1)<c:=by
    have hh:=marked_exclusion_budget_mono W Z (insert v Z) (l+12) (l+13) b c (by omega)
      (by simpa only [Nat.cast_add,Nat.cast_ofNat,add_assoc] using hbudget)
    simpa only [Nat.cast_add,Nat.cast_ofNat,add_assoc] using hh
  obtain ⟨C,hC,hav,_⟩:=marked_cycle_at_head Q hl ∅ (by simp) W (insert v Z) v (Finset.mem_insert_self _ _) (by simp) hbc
  refine ⟨C,?_⟩
  intro i
  by_cases hi:i=0
  · subst i;rw [hC];exact ⟨hvW,hvZ,hvs⟩
  · exact ⟨(hav i hi).1,fun hh=>(hav i hi).2.1 (Finset.mem_insert_of_mem hh),
      fun z hz=>(hav i hi).2.2 z (Finset.mem_insert_of_mem hz)⟩

end Oberwolfach
