module

public import Oberwolfach.MarkedWheelBalance
public import Oberwolfach.MarkedSpokeCounts
public import Oberwolfach.FiniteBasisAverages

@[expose] public section

/-! Moving a common marked cycle between two compatible hubs preserves all
rim loads and transfers the exact marked and ordinary column masses. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

abbrev CommonMarkedCycle {V U E K : Type*}
    (tail head : E → V) (ktail khead : K → V) (m : ℕ) (π : Equiv.Perm V) (b : ℕ)
    (H₀ Hₖ : V → U → Prop) (u u' : U) :=
  {C : MarkedCycleTuple tail head ktail khead m π b //
    MarkedHubCompatible H₀ Hₖ C.val u ∧ MarkedHubCompatible H₀ Hₖ C.val u'}

def commonMarkedWheelLeft {V U E K : Type*}
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
    {H₀ Hₖ : V → U → Prop} (u u' : U) :
    CommonMarkedCycle tail head ktail khead m π b H₀ Hₖ u u' ↪ MarkedWheel tail head ktail khead m π b H₀ Hₖ where
  toFun C := ⟨C.val,⟨u,C.property.1⟩⟩
  inj' C D h := Subtype.ext (congrArg Sigma.fst h)

def commonMarkedWheelRight {V U E K : Type*}
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
    {H₀ Hₖ : V → U → Prop} (u u' : U) :
    CommonMarkedCycle tail head ktail khead m π b H₀ Hₖ u u' ↪ MarkedWheel tail head ktail khead m π b H₀ Hₖ where
  toFun C := ⟨C.val,⟨u',C.property.2⟩⟩
  inj' C D h := Subtype.ext (congrArg Sigma.fst h)

def markedCommonCycleTransfer {V U E K : Type*} [Fintype V]
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
    {H₀ Hₖ : V → U → Prop} (u u' : U) : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ :=
  averagedBasisDifference (commonMarkedWheelLeft u u') (commonMarkedWheelRight u u')

theorem markedCommonCycleTransfer_rim {V U E K : Type*} [Fintype V] [Fintype U] [DecidableEq V]
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
    {H₀ Hₖ : V → U → Prop} (u u' : U) (e : E⊕K) :
    markedWheelRimLoad (markedCommonCycleTransfer (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
      (m:=m) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=Hₖ) u u') e=0 := by
  unfold markedWheelRimLoad markedCommonCycleTransfer
  rw [averagedBasisDifference_test]
  simp only [commonMarkedWheelLeft,commonMarkedWheelRight,Function.Embedding.coeFn_mk,sub_self,
    Finset.sum_const_zero,zero_div]

theorem markedCommonCycleTransfer_spoke {V U E K : Type*} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U]
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
    {H₀ Hₖ : V → U → Prop} (u u' : U) (j : Bool) (v : V) (h : U) :
    markedWheelSpokeLoad (markedCommonCycleTransfer (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
      (m:=m) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=Hₖ) u u') j v h=
      ((if h=u then (1:ℝ) else 0)-(if h=u' then 1 else 0))*
      (∑ C : CommonMarkedCycle tail head ktail khead m π b H₀ Hₖ u u',markedSpokeIndicator C.val.val j v)/
      (Fintype.card (CommonMarkedCycle tail head ktail khead m π b H₀ Hₖ u u'):ℝ) := by
  unfold markedWheelSpokeLoad markedCommonCycleTransfer
  rw [averagedBasisDifference_test]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro C _
  dsimp only [commonMarkedWheelLeft,commonMarkedWheelRight]
  split_ifs <;> simp_all

theorem markedCommonCycleTransfer_bound {V U E K : Type*} [Fintype V]
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
    {H₀ Hₖ : V → U → Prop} (u u' : U)
    (D : MarkedWheel tail head ktail khead m π b H₀ Hₖ) :
    |markedCommonCycleTransfer u u' D|≤
      2/(Fintype.card (CommonMarkedCycle tail head ktail khead m π b H₀ Hₖ u u'):ℝ) :=
  averagedBasisDifference_bound (commonMarkedWheelLeft u u') (commonMarkedWheelRight u u') D

theorem markedCommonCycleTransfer_support {V U E K : Type*} [Fintype V]
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
    {H₀ Hₖ : V → U → Prop} (u u' : U)
    (D : MarkedWheel tail head ktail khead m π b H₀ Hₖ) (hu : D.2.val≠u) (hu' : D.2.val≠u') :
    markedCommonCycleTransfer u u' D=0 := by
  apply averagedBasisDifference_zero
  · intro C he
    exact hu (congrArg (fun W => W.2.val) he)
  · intro C he
    exact hu' (congrArg (fun W => W.2.val) he)

end Oberwolfach
