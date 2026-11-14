module

public import Oberwolfach.RawIntervalTwoUnassignedProbability
public import Oberwolfach.RawIntervalUnassignedColumnCount

@[expose] public section
/-! Jointly unassigned pairs in distinct hub columns are independent even
though the two labels inside one column may have overlapping windows. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

def rawIntervalUnassignedPairColumnCount (π:Equiv.Perm V) (d:ℕ)
    (σ:RawIntervalFamilyOutcome V U Γ Color) (x y:V) (J:Finset U):ℝ:=
  ∑u∈J,if rawIntervalFamilyState π d σ (x,u)=none ∧ rawIntervalFamilyState π d σ (y,u)=none then 1 else 0

theorem raw_interval_unassigned_pair_column_tail
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (x y:V) (J:Finset U) (t:ℝ) (ht:0≤t):
    let μ:=fun u=>rawIntervalCoordinateLaw (V:=V) d hd (q u) (hq u) (hQ u) (s u) (hs u) (hS u)
    let p:=fun u=>(FiniteLaw.pi (μ u)).probability (fun σ=>rawIntervalState π d σ x=none ∧ rawIntervalState π d σ y=none)
    (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability
      (fun σ=>t≤|rawIntervalUnassignedPairColumnCount π d σ x y J-∑u∈J,p u|)≤2*Real.exp (-2*t^2/J.card) :=by
  intro μ p
  let X:=fun (_:U) (σ:RawIntervalOutcome V Γ Color)=>
    if rawIntervalState π d σ x=none ∧ rawIntervalState π d σ y=none then (1:ℝ) else 0
  letI:MeasurableSpace (RawIntervalOutcome V Γ Color):=⊤
  letI:MeasurableSingletonClass (RawIntervalOutcome V Γ Color):=⟨fun _=>trivial⟩
  have hh:=finiteLaw_bounded_coordinate_sum (fun u=>FiniteLaw.pi (μ u)) X
    (fun _=>0) (fun _=>1) J (by intro u _ σ;dsimp [X];split_ifs <;> norm_num) ht
  have hmean (u:U):(FiniteLaw.pi (μ u)).expectation (X u)=p u:=by
    dsimp only [p]
    unfold FiniteLaw.expectation FiniteLaw.probability
    dsimp only [X]
    apply Finset.sum_congr rfl
    intro σ _
    split_ifs <;> simp_all
  simp only [hmean,sub_zero,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hh
  have he:=finiteLaw_pi_blocks_probability μ (fun τ=>t≤|(∑u∈J,X u (τ u))-∑u∈J,p u|)
  rw [←he] at hh
  convert hh using 1
  dsimp only [μ,X,rawIntervalFamilyLaw,rawIntervalUnassignedPairColumnCount,rawIntervalFamilyState]
  unfold rawIntervalFamilyLaw
  rfl
end Oberwolfach
