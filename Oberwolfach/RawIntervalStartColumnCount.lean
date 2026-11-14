module

public import Oberwolfach.RawIntervalUnassignedPairColumn

@[expose] public section
/-! The same raw start, viewed across independent hub columns. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

def rawIntervalStartColumnCount (π:Equiv.Perm V) (d:ℕ)
    (σ:RawIntervalFamilyOutcome V U Γ Color) (v:V) (g:Γ) (J:Finset U):ℝ:=
  ∑u∈J,if rawIntervalColouredStart π d (fun e=>σ (u,e)) v g then 1 else 0

theorem raw_interval_start_column_tail
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (v:V) (g:Γ) (J:Finset U) (t:ℝ) (ht:0≤t):
    (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability
      (fun σ=>t≤|rawIntervalStartColumnCount π d σ v g J-∑u∈J,q u g/(d:ℝ)|)≤2*Real.exp (-2*t^2/J.card) :=by
  let μ:=fun u=>rawIntervalCoordinateLaw (V:=V) d hd (q u) (hq u) (hQ u) (s u) (hs u) (hS u)
  let X:=fun (_:U) (σ:RawIntervalOutcome V Γ Color)=>if rawIntervalColouredStart π d σ v g then (1:ℝ) else 0
  letI:MeasurableSpace (RawIntervalOutcome V Γ Color):=⊤
  letI:MeasurableSingletonClass (RawIntervalOutcome V Γ Color):=⟨fun _=>trivial⟩
  have hh:=finiteLaw_bounded_coordinate_sum (fun u=>FiniteLaw.pi (μ u)) X
    (fun _=>0) (fun _=>1) J (by intro u _ σ;dsimp [X];split_ifs <;> norm_num) ht
  have hmean (u:U):(FiniteLaw.pi (μ u)).expectation (X u)=q u g/(d:ℝ):=by
    have hp:=rawIntervalColouredStart_probability π d hd (q u) (hq u) (hQ u) (s u) (hs u) (hS u) hnoshort v g
    unfold FiniteLaw.expectation FiniteLaw.probability at *
    dsimp only [μ,X]
    convert hp using 1
    apply Finset.sum_congr rfl
    intro σ _
    split_ifs <;> simp_all
  simp only [hmean,sub_zero,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hh
  have he:=finiteLaw_pi_blocks_probability μ (fun τ=>t≤|(∑u∈J,X u (τ u))-∑u∈J,q u g/(d:ℝ)|)
  rw [←he] at hh
  convert hh using 1
  dsimp only [μ,X,rawIntervalFamilyLaw,rawIntervalStartColumnCount]
  unfold rawIntervalFamilyLaw
  rfl
end Oberwolfach
