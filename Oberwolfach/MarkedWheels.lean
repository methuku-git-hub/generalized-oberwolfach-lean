module

public import Oberwolfach.MarkedCycleRepresentation
public import Oberwolfach.MarkedPhysicalEdges
public import Oberwolfach.MarkedCycleCountBounds
public import Oberwolfach.WheelLoadCombinations

@[expose] public section

/-! Marked wheels in the canonical cycle representation. Position zero is
the head of the unique marked arc and has a marked spoke; all other spokes
have ordinary type. Rim and hub vertices live in separate types. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def MarkedHubCompatible {V U : Type*} {m : ℕ}
    (H₀ Hₖ : V → U → Prop) (C : Fin (m+1) → V) (u : U) : Prop :=
  Hₖ (C 0) u ∧ ∀ i : Fin m,H₀ (C i.succ) u

abbrev MarkedWheel {V U E K : Type*}
    (tail head : E → V) (ktail khead : K → V) (m : ℕ) (π : Equiv.Perm V) (b : ℕ)
    (H₀ Hₖ : V → U → Prop) :=
  (C : MarkedCycleTuple tail head ktail khead m π b) × {u // MarkedHubCompatible H₀ Hₖ C.val u}

def markedSpokeIndicator {V : Type*} [DecidableEq V] {m : ℕ}
    (C : Fin (m+1) → V) (j : Bool) (v : V) : ℝ :=
  if j then (if C 0=v then 1 else 0) else ∑ i : Fin m,if C i.succ=v then 1 else 0

def markedWheelRimLoad {V U E K : Type*} [Fintype V] [Fintype U] [DecidableEq V]
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
    {H₀ Hₖ : V → U → Prop}
    (ψ : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (e : E⊕K) : ℝ :=
  ∑ W,ψ W*markedCycleIncidence tail head ktail khead m W.1.val e

def markedWheelSpokeLoad {V U E K : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
    {H₀ Hₖ : V → U → Prop}
    (ψ : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (j : Bool) (v : V) (u : U) : ℝ :=
  ∑ W,ψ W*(if W.2.val=u then markedSpokeIndicator W.1.val j v else 0)

theorem markedSpokeIndicator_nonneg {V : Type*} [DecidableEq V] {m : ℕ}
    (C : Fin (m+1) → V) (j : Bool) (v : V) : 0≤markedSpokeIndicator C j v := by
  cases j
  · simp only [markedSpokeIndicator,Bool.false_eq_true,ite_false]
    exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
  · dsimp [markedSpokeIndicator];split_ifs <;> norm_num

theorem markedSpokeIndicator_total {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ}
    (C : Fin (m+1) → V) (j : Bool) :
    (∑ v,markedSpokeIndicator C j v)=if j then (1:ℝ) else m := by
  cases j
  · simp only [markedSpokeIndicator,Bool.false_eq_true,ite_false]
    rw [Finset.sum_comm]
    simp
  · simp [markedSpokeIndicator]

theorem markedHubCompatible_missing_spoke {V U : Type*} [DecidableEq V] {m : ℕ}
    (H₀ Hₖ : V → U → Prop) (C : Fin (m+1) → V) (u : U)
    (hc : MarkedHubCompatible H₀ Hₖ C u) (j : Bool) (v : V)
    (hmiss : ¬(if j then Hₖ v u else H₀ v u)) : markedSpokeIndicator C j v=0 := by
  cases j
  · simp only [markedSpokeIndicator,Bool.false_eq_true,ite_false] at *
    apply Finset.sum_eq_zero
    intro i _
    apply if_neg
    intro he
    exact hmiss (he ▸ hc.2 i)
  · simp only [markedSpokeIndicator,ite_true] at *
    apply if_neg
    intro he
    exact hmiss (he ▸ hc.1)

theorem markedWheelSpokeLoad_outside {V U E K : Type*} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U]
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
    {H₀ Hₖ : V → U → Prop}
    (ψ : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (j : Bool) (v : V) (u : U)
    (hmiss : ¬(if j then Hₖ v u else H₀ v u)) : markedWheelSpokeLoad ψ j v u=0 := by
  unfold markedWheelSpokeLoad
  apply Finset.sum_eq_zero
  intro W _
  by_cases he : W.2.val=u
  · rw [if_pos he]
    have hm : ¬(if j then Hₖ v W.2.val else H₀ v W.2.val) := by simpa only [he] using hmiss
    rw [markedHubCompatible_missing_spoke H₀ Hₖ W.1.val W.2.val W.2.property j v hm,mul_zero]
  · rw [if_neg he,mul_zero]

end Oberwolfach
