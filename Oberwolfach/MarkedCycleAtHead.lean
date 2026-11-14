module

public import Oberwolfach.MarkedCanonicalCycleCompletion
public import Oberwolfach.MarkedExclusionBudget

@[expose] public section

/-! A canonical cycle through a prescribed marked head, with optional
common spoke constraints. Only its free vertices avoid the old root set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ} {c ch:ℝ}

theorem marked_cycle_at_head
    (Q:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (hl:2≤l) (P:Finset U) (hP:P.card≤2) (W Z:Finset V) (v:V) (hv:v∈Z)
    (hvP:markedSpokesTo H₀ HK true P v)
    (hbudget:(W.card:ℝ)+(Z.card+l+12)*(2*b+1)<c):
    ∃ C:MarkedCycleTuple tail head ktail khead (l+4) π b,
      C.val 0=v∧
      (∀ i:Fin (l+5),i≠0→C.val i∉W∧C.val i∉Z∧∀ z∈Z,¬PermutationClose π b (C.val i) z)∧
      ∀ u∈P,MarkedHubCompatible H₀ HK C.val u:=by
  have hb0:(W.card:ℝ)+Z.card*(2*b+1)<c:=by
    have hh:=marked_exclusion_budget_mono W Z Z 0 (l+12) b c (by omega)
      (by simpa only [Nat.cast_add,Nat.cast_ofNat,add_assoc] using hbudget)
    simpa only [Nat.cast_zero,add_zero] using hh
  obtain ⟨x,hx,hxW,hxZ,hxs⟩:=marked_candidate_avoiding (π:=π)
    (Finset.univ.filter (fun x=>markedArcPresent tail head ktail khead false v x∧markedSpokesTo H₀ HK false P x))
    W Z (Q.outgoing false false v P hP) hb0
  have hb1:(W.card:ℝ)+(insert x Z).card*(2*b+1)<c:=by
    have hi:=Finset.card_insert_le x Z
    have hh:=marked_exclusion_budget_mono W Z (insert x Z) 0 (l+12) b c (by omega)
      (by simpa only [Nat.cast_add,Nat.cast_ofNat,add_assoc] using hbudget)
    simpa only [Nat.cast_zero,add_zero] using hh
  obtain ⟨y,hy,hyW,hyZ,hys⟩:=marked_candidate_avoiding (π:=π)
    (Finset.univ.filter (fun y=>markedArcPresent tail head ktail khead true y v∧markedSpokesTo H₀ HK false P y))
    W (insert x Z) (Q.incoming true false v P hP) hb1
  have hxy:¬PermutationClose π b x y:=fun hh=>hys x (Finset.mem_insert_self _ _) ((permutationClose_symm π b _ _).mp hh)
  have hbpath:(W.card:ℝ)+(Z.card+l+5)*(2*b+1)<c:=by
    have hh:=marked_exclusion_budget_mono W Z Z (l+5) (l+12) b c (by omega)
      (by simpa only [Nat.cast_add,Nat.cast_ofNat,add_assoc] using hbudget)
    simpa only [Nat.cast_add,Nat.cast_ofNat,add_assoc] using hh
  obtain ⟨p,C,hC,hp0,hpn,hpa,hCP⟩:=marked_canonical_cycle_completion Q hl P hP W Z v x y hv hxy
    (Finset.mem_filter.mp hx).2.1 (Finset.mem_filter.mp hy).2.1 hvP
    (Finset.mem_filter.mp hx).2.2 (Finset.mem_filter.mp hy).2.2 hxW hyW hxZ
    (fun hz=>hyZ (Finset.mem_insert_of_mem hz)) hxs (fun z hz=>hys z (Finset.mem_insert_of_mem hz)) hbpath
  refine ⟨C,by simpa only [hC,Fin.cons_zero],?_,hCP⟩
  intro i;refine Fin.cases ?_ (fun j=>?_) i
  · intro h;exact False.elim (h rfl)
  · intro h;simpa only [hC,Fin.cons_succ] using hpa j

end Oberwolfach
