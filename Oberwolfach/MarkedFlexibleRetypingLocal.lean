module

public import Oberwolfach.MarkedIndegreeCorrection
public import Oberwolfach.UniformIncomingRoundingLocal

@[expose] public section
/-! Correct indegrees with small physical load away from a set of exceptional heads. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V E : Type} [Fintype V] [Fintype E] [Nonempty V]

theorem marked_flexible_retyping_local
    (tail head:E→V) (M₀:E→Bool) (A:E→Prop) (b:ℕ) (rho eta:ℝ)
    (hrho:0<rho) (heta:0<eta) (hetaR:eta≤rho)
    (I:Finset V) (loc:ℝ) (hloc:0≤loc)
    (hdevlocal:∀v,v∉I→|(markedHeadCount head M₀ v:ℝ)-(b:ℝ)|≤loc)
    (hpair:Function.Injective (fun e:E=>(tail e,head e)))
    (hdev:∀ v, |(markedHeadCount head M₀ v:ℝ)-(b:ℝ)|≤eta*Fintype.card V)
    (hmarked:∀ v, rho*Fintype.card V≤(markedFlexibleIncoming head M₀ A v true:ℝ))
    (hunmarked:∀ v, rho*Fintype.card V≤(markedFlexibleIncoming head M₀ A v false:ℝ)) :
    ∃ M:E→Bool,
      (∀ v, markedHeadCount head M v=b) ∧
      (∀ e, M e≠M₀ e → A e) ∧
      (∀ v, ((∑ e, if head e=v ∧ M e≠M₀ e then (1:ℕ) else 0):ℝ)≤eta*Fintype.card V) ∧
      (∀ v,v∉I→((∑ e, if head e=v ∧ M e≠M₀ e then (1:ℕ) else 0):ℝ)≤loc) ∧
      (∀ v, (∑ e, if tail e=v ∧ M e≠M₀ e then (1:ℕ) else 0) ≤
        ⌈(I.card:ℝ)*(eta*Fintype.card V/(rho*Fintype.card V))+
          (Fintype.card V:ℝ)*(loc/(rho*Fintype.card V))⌉₊) := by
  let n : ℝ := Fintype.card V
  let deg : V→ℕ := markedHeadCount head M₀
  let t : V→ℕ := fun v=>markedDeviation (deg v) b
  let choose : E→Prop := fun e=>A e ∧ if b<deg (head e) then M₀ e=true else M₀ e=false
  have hn : 0<n := by dsimp [n]; exact_mod_cast Fintype.card_pos
  have hτ : 0≤eta*n := mul_nonneg heta.le hn.le
  have hρn : 0<rho*n := mul_pos hrho hn
  have htBound : ∀v,(t v:ℝ)≤eta*n := by
    intro v
    change (markedDeviation (markedHeadCount head M₀ v) b:ℝ)≤eta*Fintype.card V
    rw [marked_deviation_cast_abs]
    exact hdev v
  have hsize : ∀v,rho*n≤((eligibleIncoming head choose v).card:ℝ) := by
    intro v
    by_cases hv : b<deg v
    · have heq : eligibleIncoming head choose v =
          Finset.univ.filter (fun e=>A e ∧ head e=v ∧ M₀ e=true) := by
        ext e
        simp only [eligibleIncoming,Finset.mem_filter,Finset.mem_univ,true_and,choose]
        by_cases he:head e=v <;> simp [he,hv,deg]
      simpa only [heq,markedFlexibleIncoming,n] using hmarked v
    · have heq : eligibleIncoming head choose v =
          Finset.univ.filter (fun e=>A e ∧ head e=v ∧ M₀ e=false) := by
        ext e
        simp only [eligibleIncoming,Finset.mem_filter,Finset.mem_univ,true_and,choose]
        by_cases he:head e=v <;> simp [he,hv,deg]
      simpa only [heq,markedFlexibleIncoming,n] using hunmarked v
  have ht : ∀v,t v≤(eligibleIncoming head choose v).card := by
    intro v
    have hh : (t v:ℝ)≤((eligibleIncoming head choose v).card:ℝ) :=
      (htBound v).trans ((mul_le_mul_of_nonneg_right hetaR hn.le).trans (hsize v))
    exact_mod_cast hh
  have htLocal:∀v,v∉I→(t v:ℝ)≤loc:=by
    intro v hv
    change (markedDeviation (markedHeadCount head M₀ v) b:ℝ)≤loc
    rw [marked_deviation_cast_abs]
    exact hdevlocal v hv
  obtain ⟨D,hD,hheads,htails⟩ := uniform_incoming_rounding_local tail head choose t I ht
    (eta*n) loc (rho*n) hτ hloc hρn htBound htLocal hsize hpair
  refine ⟨flipMarkedArcs M₀ D, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    by_cases hv : b<deg v
    · have hs : ∀ e,head e=v→D e=true→M₀ e=true := by
        intro e he hd
        have hh:=hD e hd
        simpa only [choose,he,hv,if_pos,true_and] using hh.2
      have hr := marked_indegree_flip_reduces head M₀ D v hs
      have hold : (∑ e, if head e=v ∧ M₀ e=true then (1:ℤ) else 0)=(deg v:ℤ) := by
        dsimp [deg,markedHeadCount]; push_cast; rfl
      have hsel : (∑ e, if head e=v ∧ D e=true then (1:ℤ) else 0)=(t v:ℤ) := by
        exact_mod_cast hheads v
      rw [hold,hsel] at hr
      have hsub : (t v:ℤ)=(deg v:ℤ)-(b:ℤ) := by
        dsimp [t,markedDeviation]; rw [if_pos hv, Nat.cast_sub (Nat.le_of_lt hv)]
      rw [hsub] at hr
      have : (∑ e, if head e=v ∧ flipMarkedArcs M₀ D e=true then (1:ℤ) else 0) = b := by linarith
      change markedHeadCount head (flipMarkedArcs M₀ D) v=b
      dsimp [markedHeadCount]
      exact_mod_cast this
    · have hs : ∀ e,head e=v→D e=true→M₀ e=false := by
        intro e he hd
        have hh:=hD e hd
        simpa only [choose,he,hv,if_false,true_and] using hh.2
      have hr := marked_indegree_flip_increases head M₀ D v hs
      have hold : (∑ e, if head e=v ∧ M₀ e=true then (1:ℤ) else 0)=(deg v:ℤ) := by
        dsimp [deg,markedHeadCount]; push_cast; rfl
      have hsel : (∑ e, if head e=v ∧ D e=true then (1:ℤ) else 0)=(t v:ℤ) := by
        exact_mod_cast hheads v
      rw [hold,hsel] at hr
      have hsub : (t v:ℤ)=(b:ℤ)-(deg v:ℤ) := by
        dsimp [t,markedDeviation]; rw [if_neg hv, Nat.cast_sub (by omega)]
      rw [hsub] at hr
      have : (∑ e, if head e=v ∧ flipMarkedArcs M₀ D e=true then (1:ℤ) else 0) = b := by linarith
      change markedHeadCount head (flipMarkedArcs M₀ D) v=b
      dsimp [markedHeadCount]
      exact_mod_cast this
  · intro e he
    have hd : D e=true := by
      cases hde:D e <;> cases hme:M₀ e <;> simp_all [flipMarkedArcs]
    exact (hD e hd).1
  · intro v
    have heq : (∑ e, if head e=v ∧ flipMarkedArcs M₀ D e≠M₀ e then (1:ℕ) else 0) =
        ∑ e, if head e=v ∧ D e=true then (1:ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      cases hde:D e <;> cases hme:M₀ e <;> simp [flipMarkedArcs,hde,hme]
    have hh := congrArg (fun x:ℕ => (x:ℝ)) (heq.trans (hheads v))
    simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] at hh
    simpa only [Nat.cast_one, Nat.cast_zero] using le_of_eq_of_le hh (htBound v)
  · intro v hv
    have heq : (∑ e, if head e=v ∧ flipMarkedArcs M₀ D e≠M₀ e then (1:ℕ) else 0) =
        ∑ e, if head e=v ∧ D e=true then (1:ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      cases hde:D e <;> cases hme:M₀ e <;> simp [flipMarkedArcs,hde,hme]
    have hh := congrArg (fun x:ℕ => (x:ℝ)) (heq.trans (hheads v))
    simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] at hh
    simpa only [Nat.cast_one, Nat.cast_zero] using le_of_eq_of_le hh (htLocal v hv)
  · intro v
    have heq : (∑ e, if tail e=v ∧ flipMarkedArcs M₀ D e≠M₀ e then (1:ℕ) else 0) =
        ∑ e, if tail e=v ∧ D e=true then (1:ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      cases hde:D e <;> cases hme:M₀ e <;> simp [flipMarkedArcs,hde,hme]
    rw [heq]
    exact htails v
end Oberwolfach
