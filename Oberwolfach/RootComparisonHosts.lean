module

public import Oberwolfach.OrdinaryWheelRestriction
public import Oberwolfach.OrdinaryHubWheelPacking
public import Oberwolfach.InducedFractionalCycles

@[expose] public section

/-! Restoring edges at earlier row roots is harmless only because the
new wheel avoids those roots. These results prove the physical
edge-disjointness and the degree bounds for the comparison deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {Q F:SimpleGraph V} {H:V→U→Prop} {r:ℕ}

def ordinaryPackingSpokes (M:Finset (OrdinaryWheel Q F H r)) (v:V) (u:U) : Prop :=
  ∃ W∈M,ordinaryWheelHub W=u ∧ v∈(ordinaryWheelRim W).support

theorem ordinaryPackingSpokes_iff (M:Finset (OrdinaryWheel Q F H r)) (v:V) (u:U) :
    ordinaryPackingSpokes M v u ↔ Sum.inr (v,u)∈M.biUnion ordinaryWheelResources := by
  simp only [ordinaryPackingSpokes,Finset.mem_biUnion,ordinaryWheelResources_spoke]

theorem spanningRestriction_degree_bound (G:SimpleGraph V) (A:Finset V) (L:ℝ) (hL:0≤L)
    (hG:∀ a∈A,(G.degree a:ℝ)≤L) (a:V) : (spanningRestriction G A).degree a≤L := by
  by_cases ha:a∈A
  · exact (Nat.cast_le.mpr (SimpleGraph.degree_le_of_le (spanningRestriction_le G A))).trans (hG a ha)
  · have hzero:(spanningRestriction G A).degree a=0:=by
      rw [←SimpleGraph.card_neighborFinset_eq_degree,Finset.card_eq_zero]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro b hb
      exact ha ((spanningRestriction_adj G A a b).mp (((spanningRestriction G A).mem_neighborFinset a b).mp hb)).2.1
    rw [hzero,Nat.cast_zero];exact hL

theorem restricted_spoke_row_bound (E:V→U→Prop) (A:Finset V) (L:ℝ) (hL:0≤L)
    (hE:∀ a∈A,((Finset.univ.filter (E a)).card:ℝ)≤L) (a:V) :
    ((Finset.univ.filter (fun u=>a∈A∧E a u)).card:ℝ)≤L := by
  by_cases ha:a∈A
  · simpa only [ha,true_and] using hE a ha
  · simpa only [ha,false_and,Finset.filter_false,Finset.card_empty,Nat.cast_zero] using hL

theorem restricted_spoke_column_bound (E:V→U→Prop) (A:Finset V) (L:ℝ)
    (hE:∀ u,((Finset.univ.filter (fun a=>E a u)).card:ℝ)≤L) (u:U) :
    ((Finset.univ.filter (fun a=>a∈A∧E a u)).card:ℝ)≤L := by
  apply le_trans _ (hE u)
  exact Nat.cast_le.mpr (Finset.card_le_card (by intro a ha;exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp ha).2.2⟩))

theorem ordinary_wheel_comparison_disjoint (M:Finset (OrdinaryWheel Q F H r)) (A:Finset V) (x:V)
    (hM:∀ W∈M,x∉(ordinaryWheelRim W).support)
    (C:OrdinaryWheel (Q\spanningRestriction (ordinaryWheelRimGraph M) A) F
      (fun v u=>H v u∧¬(v∈A∧ordinaryPackingSpokes M v u)) r)
    (hC:∀ a∈(ordinaryWheelRim C).support,a=x∨a∈A) :
    Disjoint (ordinaryWheelResources C) (M.biUnion ordinaryWheelResources) := by
  apply Finset.disjoint_left.mpr
  intro e he heM
  obtain ⟨W,hW,hew⟩:=Finset.mem_biUnion.mp heM
  cases e with
  | inl e =>
    rw [ordinaryWheelResources_rim] at he hew
    induction e using Sym2.inductionOn with
    | _ a b =>
      have ha:a∈A:=by
        rcases hC a he.mem_support_left with rfl|ha
        · exact (hM W hW hew.mem_support_left).elim
        · exact ha
      have hb:b∈A:=by
        rcases hC b he.mem_support_right with rfl|hb
        · exact (hM W hW hew.mem_support_right).elim
        · exact hb
      have hprev:(ordinaryWheelRimGraph M).Adj a b:=SimpleGraph.iSup_adj.mpr ⟨W,SimpleGraph.iSup_adj.mpr ⟨hW,hew⟩⟩
      have hd:(spanningRestriction (ordinaryWheelRimGraph M) A).Adj a b:=(spanningRestriction_adj _ A a b).mpr ⟨hprev,ha,hb⟩
      exact (C.val.1.property he).2 hd
  | inr vu =>
    rw [ordinaryWheelResources_spoke] at he hew
    have ha:vu.1∈A:=by
      rcases hC vu.1 he.2 with ha|ha
      · rw [ha] at hew;exact (hM W hW hew.2).elim
      · exact ha
    have hprev:ordinaryPackingSpokes M vu.1 (ordinaryWheelHub C):=
      ⟨W,hW,hew.1.trans he.1.symm,hew.2⟩
    exact (C.property.1 vu.1 he.2).2 ⟨ha,hprev⟩

end Oberwolfach
