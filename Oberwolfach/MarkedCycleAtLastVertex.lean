module

public import Oberwolfach.MarkedTransformerRimCycles
public import Oberwolfach.MarkedHostGreedyChoices
public import Oberwolfach.MarkedExclusionBudget

@[expose] public section

/-! A canonical marked cycle through the prescribed tail of its marked arc.
The other endpoint and all remaining vertices are constructed from host
counts and avoid the old root set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ} {c ch:ℝ}

theorem marked_cycle_at_last_vertex
    (Q:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (hl:2≤l) (W Z:Finset V) (v:V) (hv:v∈Z)
    (hbudget:(W.card:ℝ)+(Z.card+l+12)*(2*b+1)<c):
    ∃ C:MarkedCycleTuple tail head ktail khead (l+4) π b,
      C.val (Fin.last (l+4))=v∧
      ∀ i,i≠Fin.last (l+4)→C.val i∉W∧C.val i∉Z∧∀ z∈Z,¬PermutationClose π b (C.val i) z:=by
  have hb0:(W.card:ℝ)+Z.card*(2*b+1)<c:=by
    have hh:=marked_exclusion_budget_mono W Z Z 0 (l+12) b c (by omega)
      (by simpa only [Nat.cast_add,Nat.cast_ofNat,add_assoc] using hbudget)
    simpa using hh
  obtain ⟨w,hw,hwW,hwZ,hws⟩:=marked_candidate_avoiding (π:=π)
    (Finset.univ.filter (fun w=>markedArcPresent tail head ktail khead true v w∧markedSpokesTo H₀ HK false ∅ w))
    W Z (Q.outgoing true false v ∅ (by simp)) hb0
  have hvw:¬PermutationClose π b v w:=fun hh=>hws v hv ((permutationClose_symm π b _ _).mp hh)
  have hi:=Finset.card_insert_le w Z
  have hbpath:(W.card:ℝ)+((insert w Z).card+l+4)*(2*b+1)<c:=by
    have hh:=marked_exclusion_budget_mono W Z (insert w Z) (l+4) (l+12) b c (by omega)
      (by simpa only [Nat.cast_add,Nat.cast_ofNat,add_assoc] using hbudget)
    simpa only [Nat.cast_add,Nat.cast_ofNat,add_assoc] using hh
  obtain ⟨p,C,D,hC,_,hpa,_⟩:=marked_transformer_rim_cycles tail head ktail khead π b l hl v w v w true W (insert w Z)
    (Finset.mem_insert_of_mem hv) (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hv) (Finset.mem_insert_self _ _)
    hvw hvw c
    (by have hh:∃ e,ktail e=v∧khead e=w:=(Finset.mem_filter.mp hw).2.1;exact ⟨hh,hh⟩)
    (by simpa only [markedArcPresent,Bool.false_eq_true,ite_false,markedSpokesTo_empty,and_true,and_self] using Q.outgoing false false w ∅ (by simp))
    (by simpa only [markedArcPresent,Bool.false_eq_true,ite_false,markedSpokesTo_empty,and_true,and_self] using Q.incoming false false v ∅ (by simp))
    (by intro j x;simpa only [markedArcPresent,markedSpokesTo_empty,and_true] using Q.outgoing j false x ∅ (by simp))
    (by intro x y hxy;simpa only [markedArcPresent,Bool.false_eq_true,ite_false,markedSpokesTo_empty,and_true] using Q.twoStep false x y ∅ hxy (by simp)) hbpath
  have hC':∀ i,C.val i=Fin.cons (α:=fun _=>V) v (Fin.cons w p) (canonicalMarkedRotation 0 i):=by
    simpa only [ite_true] using hC
  refine ⟨C,by simp only [hC',canonicalMarkedRotation_last,Fin.cons_zero],?_⟩
  intro i hi
  have hrot:canonicalMarkedRotation (0:Fin (l+5)) i≠0:=by
    intro he
    apply hi
    exact (canonicalMarkedRotation (0:Fin (l+5))).injective (he.trans (canonicalMarkedRotation_last 0).symm)
  rw [hC']
  generalize hj:canonicalMarkedRotation (0:Fin (l+5)) i=j at hrot ⊢
  revert hrot
  refine Fin.cases ?_ (fun k=>?_) j
  · intro h;exact False.elim (h rfl)
  · intro h
    rw [Fin.cons_succ]
    refine Fin.cases ?_ (fun a=>?_) k
    · exact ⟨hwW,hwZ,hws⟩
    · simp only [Fin.cons_succ]
      exact ⟨(hpa a).1,fun hh=>(hpa a).2.1 (Finset.mem_insert_of_mem hh),
        fun z hz=>(hpa a).2.2 z (Finset.mem_insert_of_mem hz)⟩

end Oberwolfach
