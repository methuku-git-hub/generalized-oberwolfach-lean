module

public import Oberwolfach.RawIntervalUnassignedProbability
public import Oberwolfach.FiniteProductBlocks

@[expose] public section
/-! For a fixed label, unassigned states in distinct hub columns are
independent. The set of hubs is fixed before exposure. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

def rawIntervalUnassignedColumnCount (π:Equiv.Perm V) (d:ℕ)
    (σ:RawIntervalFamilyOutcome V U Γ Color) (v:V) (J:Finset U):ℝ:=
  ∑ u∈J,if rawIntervalFamilyState π d σ (v,u)=none then 1 else 0

theorem rawIntervalUnassignedColumnCount_tail
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x) (v:V) (J:Finset U) (t:ℝ) (ht:0≤t):
    (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability
      (fun σ=>t≤|rawIntervalUnassignedColumnCount π d σ v J-
        ∑ u∈J,(1-(∑ g,q u g)-(∑ j,s u j))|)≤2*Real.exp (-2*t^2/J.card) := by
  let μ:=fun u=>rawIntervalCoordinateLaw (V:=V) d hd (q u) (hq u) (hQ u) (s u) (hs u) (hS u)
  let X:=fun (_:U) (σ:RawIntervalOutcome V Γ Color)=>if rawIntervalState π d σ v=none then (1:ℝ) else 0
  letI:MeasurableSpace (RawIntervalOutcome V Γ Color):=⊤
  letI:MeasurableSingletonClass (RawIntervalOutcome V Γ Color):=⟨fun _=>trivial⟩
  have hh:=finiteLaw_bounded_coordinate_sum (fun u=>FiniteLaw.pi (μ u)) X
    (fun _=>0) (fun _=>1) J (by intro u _ σ;dsimp [X];split_ifs <;> norm_num) ht
  have hmean (u:U):(FiniteLaw.pi (μ u)).expectation (X u)=1-(∑ g,q u g)-(∑ j,s u j):=by
    have hp:=rawIntervalFamily_unassigned_probability π d hd q hq hQ s hs hS hnoshort (v,u)
    dsimp only [rawIntervalFamilyState] at hp
    rw [rawIntervalFamily_column_event d hd q hq hQ s hs hS u
      (fun τ=>rawIntervalState π d τ v=none)] at hp
    unfold FiniteLaw.expectation FiniteLaw.probability at *
    dsimp only [μ,X]
    convert hp using 1
    apply Finset.sum_congr rfl
    intro σ _
    split_ifs <;> simp_all
  simp only [hmean,sub_zero,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hh
  have he:=finiteLaw_pi_blocks_probability μ (fun τ=>t≤|(∑ u∈J,X u (τ u))-
    (∑ u∈J,(1-(∑ g,q u g)-(∑ j,s u j)))|)
  rw [←he] at hh
  convert hh using 1
  dsimp only [μ,X,rawIntervalFamilyLaw,rawIntervalUnassignedColumnCount,rawIntervalFamilyState]
  unfold rawIntervalFamilyLaw
  rfl
end Oberwolfach
