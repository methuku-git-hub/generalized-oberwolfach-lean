module

public import Oberwolfach.TransferDeletionCounts
public import Oberwolfach.FiniteConfigurationLoss

@[expose] public section

/-! Actual transfer configurations surviving sparse rim and spoke deletions.
The two root spokes are required to survive; only other required incidences
can then remove a configuration. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U : Type*} [Fintype V] [DecidableEq V]
  {r : ℕ} {hr : 3≤r} {Q F : SimpleGraph V} {H : V → U → Prop}
  {v : V} {u u' : U}

def TransferAvoids (T : OrdinaryTransferConfiguration hr Q F H v u u')
    (D : SimpleGraph V) (E : V → U → Prop) : Prop :=
  (∀ x∈insert v (Set.range T.labels),∀ y∈insert v (Set.range T.labels),¬D.Adj x y) ∧
    (∀ z∈Set.range T.labels,¬E z u ∧ ¬E z u')

def transferAfterDeletion (D : SimpleGraph V) (E : V → U → Prop)
    (hroot : ¬E v u ∧ ¬E v u')
    (T : {T : OrdinaryTransferConfiguration hr Q F H v u u' // TransferAvoids T D E}) :
    OrdinaryTransferConfiguration hr (Q \ D) F (fun z a=>H z a ∧ ¬E z a) v u u' where
  labels := T.val.labels
  omitted := T.val.omitted
  rim_edges := by
    intro j x y hxy
    refine ⟨T.val.rim_edges j hxy,?_⟩
    exact T.property.1 x (transferCycleGraph_support_subset hr T.val.labels v T.val.omitted j hxy.mem_support_left)
      y (transferCycleGraph_support_subset hr T.val.labels v T.val.omitted j hxy.mem_support_right)
  spokes := by
    intro z hz
    have hh := T.val.spokes z hz
    have he : ¬E z u ∧ ¬E z u' := by
      rcases Set.mem_insert_iff.mp hz with rfl|hz
      · exact hroot
      · exact T.property.2 z hz
    exact ⟨⟨hh.1,he.1⟩,⟨hh.2,he.2⟩⟩
  independent := T.val.independent

theorem transferAfterDeletion_injective (D : SimpleGraph V) (E : V → U → Prop)
    (hroot : ¬E v u ∧ ¬E v u') :
    Function.Injective (transferAfterDeletion (hr:=hr) (Q:=Q) (F:=F) (H:=H) D E hroot) := by
  intro T T' he
  apply Subtype.ext
  apply OrdinaryTransferConfiguration.labels_injective
  exact congrArg (fun S=>(S.labels : Fin r × Fin r → V)) he

/-- A failed avoidance condition exhibits a particular deleted edge or
spoke, counted against this same original labelled configuration. -/
theorem transfer_avoidance_failure_bound
    (T : OrdinaryTransferConfiguration hr Q F H v u u')
    (D : SimpleGraph V) (E : V → U → Prop) :
    (if TransferAvoids T D E then (0 : ℝ) else 1)≤
      (∑ x,∑ y,if D.Adj x y then
        (if x∈insert v (Set.range T.labels) ∧ y∈insert v (Set.range T.labels) then (1 : ℝ) else 0) else 0)+
      (∑ z,if E z u then (if z∈Set.range T.labels then (1 : ℝ) else 0) else 0)+
      (∑ z,if E z u' then (if z∈Set.range T.labels then (1 : ℝ) else 0) else 0) := by
  classical
  have hR : (0 : ℝ)≤∑ x,∑ y,if D.Adj x y then
      (if x∈insert v (Set.range T.labels) ∧ y∈insert v (Set.range T.labels) then (1 : ℝ) else 0) else 0 := by
    apply Finset.sum_nonneg;intro x _;apply Finset.sum_nonneg;intro y _;split_ifs <;> norm_num
  have hS (a : U) : (0 : ℝ)≤∑ z,if E z a then (if z∈Set.range T.labels then (1 : ℝ) else 0) else 0 := by
    apply Finset.sum_nonneg;intro z _;split_ifs <;> norm_num
  by_cases hg : TransferAvoids T D E
  · rw [if_pos hg]
    linarith [hS u,hS u']
  rw [if_neg hg]
  change ¬(_ ∧ _) at hg
  rcases not_and_or.mp hg with hg|hg
  · push_neg at hg
    obtain ⟨x,hx,y,hy,hxy⟩ := hg
    have hin := Finset.single_le_sum (s:=Finset.univ) (a:=y)
      (f:=fun y=>if D.Adj x y then
        (if x∈insert v (Set.range T.labels) ∧ y∈insert v (Set.range T.labels) then (1 : ℝ) else 0) else 0)
      (fun y _=>by split_ifs <;> norm_num) (Finset.mem_univ _)
    have hout := Finset.single_le_sum (s:=Finset.univ) (a:=x)
      (f:=fun x=>∑ y,if D.Adj x y then
        (if x∈insert v (Set.range T.labels) ∧ y∈insert v (Set.range T.labels) then (1 : ℝ) else 0) else 0)
      (fun x _=>by apply Finset.sum_nonneg;intro y _;split_ifs <;> norm_num) (Finset.mem_univ _)
    simp only [hxy,hx,hy,and_self,ite_true,true_and] at hin
    simp only [hx,true_and] at hout
    linarith [hS u,hS u']
  · push_neg at hg
    obtain ⟨z,hz,hz'⟩ := hg
    have hOne (a : U) (ha : E z a) : (1 : ℝ)≤∑ z,if E z a then (if z∈Set.range T.labels then (1 : ℝ) else 0) else 0 := by
      have hh := Finset.single_le_sum (s:=Finset.univ) (a:=z)
        (f:=fun z=>if E z a then (if z∈Set.range T.labels then (1 : ℝ) else 0) else 0)
        (fun z _=>by split_ifs <;> norm_num) (Finset.mem_univ _)
      simpa only [ha,hz,ite_true] using hh
    by_cases hzu : E z u
    · linarith [hOne u hzu,hS u']
    · have hzu' : E z u' := hz' hzu
      linarith [hOne u' hzu',hS u]

theorem transfer_deleted_spoke_count (E : V → U → Prop) (a : U) (d : ℝ)
    (hE : (∑ z,bipAdj E z a)≤d) :
    (∑ z,if E z a then
      (∑ T : OrdinaryTransferConfiguration hr Q F H v u u',if z∈Set.range T.labels then (1 : ℝ) else 0)
      else 0)≤d*(r : ℝ)^2*(Fintype.card V : ℝ)^(r^2-1) := by
  let M : ℝ := (r : ℝ)^2*(Fintype.card V : ℝ)^(r^2-1)
  have hM : 0≤M := by dsimp [M];positivity
  calc
    _ ≤ ∑ z,bipAdj E z a*M := by
      apply Finset.sum_le_sum
      intro z _
      by_cases hz : E z a
      · simp only [hz,ite_true,bipAdj,one_mul]
        exact transfer_free_vertex_count z
      · simp only [hz,ite_false,bipAdj,zero_mul,le_refl]
    _ = (∑ z,bipAdj E z a)*M := (Finset.sum_mul _ _ _).symm
    _ ≤ d*M := mul_le_mul_of_nonneg_right hE hM
    _ = _ := by dsimp [M];ring


/-- Sparse physical deletions remove at most O(d n^(r^2-1)) of the
original labelled transfer configurations at surviving root spokes. -/
theorem ordinary_transfer_deletion_stability
    (D : SimpleGraph V) (E : V → U → Prop) (d : ℝ)
    (hd : 0≤d) (hn : 0<Fintype.card V)
    (hD : ∀ x,(D.degree x : ℝ)≤d)
    (hE : ∀ a,(∑ z,bipAdj E z a)≤d)
    (hroot : ¬E v u ∧ ¬E v u') :
    (Fintype.card (OrdinaryTransferConfiguration hr Q F H v u u') : ℝ)-
      Fintype.card (OrdinaryTransferConfiguration hr (Q \ D) F (fun z a=>H z a ∧ ¬E z a) v u u')≤
        5*(r : ℝ)^4*d*(Fintype.card V : ℝ)^(r^2-1) := by
  classical
  let A := OrdinaryTransferConfiguration hr Q F H v u u'
  have hstart := finite_configuration_loss (fun T : A=>TransferAvoids T D E)
    (transferAfterDeletion D E hroot) (transferAfterDeletion_injective D E hroot)
  have hR := transfer_deleted_rim_count (hr:=hr) (Q:=Q) (F:=F) (H:=H) (v:=v) (u:=u) (u':=u') D d hD hn
  have hS (a : U) := transfer_deleted_spoke_count (hr:=hr) (Q:=Q) (F:=F) (H:=H) (v:=v) (u:=u) (u':=u') E a d (hE a)
  have hRcomm : (∑ T : A,∑ x,∑ y,if D.Adj x y then
      (if x∈insert v (Set.range T.labels) ∧ y∈insert v (Set.range T.labels) then (1 : ℝ) else 0) else 0)=
      (∑ x,∑ y,if D.Adj x y then
      (∑ T : A,if x∈insert v (Set.range T.labels) ∧ y∈insert v (Set.range T.labels) then (1 : ℝ) else 0) else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hxy : D.Adj x y <;> simp only [hxy,ite_true,ite_false,Finset.sum_const_zero]
  have hScomm (a : U) : (∑ T : A,∑ z,if E z a then
      (if z∈Set.range T.labels then (1 : ℝ) else 0) else 0)=
      (∑ z,if E z a then (∑ T : A,if z∈Set.range T.labels then (1 : ℝ) else 0) else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : E z a <;> simp only [hz,ite_true,ite_false,Finset.sum_const_zero]
  apply hstart.trans
  calc
    _ ≤ ∑ T : A,((∑ x,∑ y,if D.Adj x y then
      (if x∈insert v (Set.range T.labels) ∧ y∈insert v (Set.range T.labels) then (1 : ℝ) else 0) else 0)+
      (∑ z,if E z u then (if z∈Set.range T.labels then (1 : ℝ) else 0) else 0)+
      (∑ z,if E z u' then (if z∈Set.range T.labels then (1 : ℝ) else 0) else 0)) :=
        Finset.sum_le_sum (fun T _=>transfer_avoidance_failure_bound T D E)
    _ ≤ 3*(r : ℝ)^4*d*(Fintype.card V : ℝ)^(r^2-1)+
        d*(r : ℝ)^2*(Fintype.card V : ℝ)^(r^2-1)+
        d*(r : ℝ)^2*(Fintype.card V : ℝ)^(r^2-1) := by
      simp only [Finset.sum_add_distrib,hRcomm,hScomm]
      exact add_le_add (add_le_add hR (hS u)) (hS u')
    _ ≤ _ := by
      have hr1 : (1 : ℝ)≤r := by exact_mod_cast (show 1≤r by omega)
      have hp : (r : ℝ)^2≤(r : ℝ)^4 := pow_le_pow_right₀ hr1 (by omega)
      have hh := mul_le_mul_of_nonneg_right hp
        (mul_nonneg hd (pow_nonneg (Nat.cast_nonneg (α:=ℝ) (Fintype.card V)) (r^2-1)))
      nlinarith

end Oberwolfach
