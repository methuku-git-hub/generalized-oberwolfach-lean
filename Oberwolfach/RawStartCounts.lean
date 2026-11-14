module

public import Oberwolfach.FiniteProductBlocks
public import Oberwolfach.RetainedIntervalFamily

@[expose] public section

/-! The raw number of eligible hubs at each start concentrates before
retention. Hub columns are independent in the original interval law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem rawStartHubSet_tail (π : Equiv.Perm V) (d : ℕ) (hd : 2≤d)
    (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort : ∀ x l,0<l → l<2*d+1 → (π^l) x≠x)
    (g : Γ) (a : V) (t : ℝ) (ht : 0≤t) :
    (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability
      (fun σ=>t≤|((rawStartHubSet π d σ g a).card:ℝ)-(∑ u,q u g/(d:ℝ))|)≤
      2*Real.exp (-2*t^2/Fintype.card U) := by
  let μ := fun u=>rawIntervalCoordinateLaw (V:=V) d hd (q u) (hq u) (hQ u) (s u) (hs u) (hS u)
  let X := fun (_ : U) (σ : RawIntervalOutcome V Γ Color)=>if rawIntervalColouredStart π d σ a g then (1:ℝ) else 0
  letI : MeasurableSpace (RawIntervalOutcome V Γ Color) := ⊤
  letI : MeasurableSingletonClass (RawIntervalOutcome V Γ Color) := ⟨fun _=>trivial⟩
  have ht' := finiteLaw_bounded_coordinate_sum (fun u=>FiniteLaw.pi (μ u)) X
    (fun _=>0) (fun _=>1) Finset.univ
    (by intro u _ σ;dsimp [X];split_ifs <;> norm_num) ht
  have hmean (u : U) : (FiniteLaw.pi (μ u)).expectation (X u)=q u g/(d:ℝ) := by
    have hh := rawIntervalColouredStart_probability π d hd (q u) (hq u) (hQ u) (s u) (hs u) (hS u) hnoshort a g
    simpa only [μ,X,FiniteLaw.expectation,FiniteLaw.probability,mul_ite,mul_one,mul_zero] using hh
  simp only [hmean,sub_zero,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at ht'
  have he := finiteLaw_pi_blocks_probability μ (fun τ=>t≤|(∑ u,X u (τ u))-(∑ u,q u g/(d:ℝ))|)
  rw [← he] at ht'
  convert ht' using 1 <;>
    simp only [μ,X,rawIntervalFamilyLaw,rawStartHubSet,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rfl

theorem rawStartHubSet_common_event (π : Equiv.Perm V) (d : ℕ) (hd : 2≤d)
    (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort : ∀ x l,0<l → l<2*d+1 → (π^l) x≠x)
    (g : Γ) (t₀ : ℝ) (hg : ∀ u,q u g=t₀) (t : ℝ) (ht : 0<t) :
    1-2*Fintype.card V*Real.exp (-2*t^2/Fintype.card U)≤
    (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability
      (fun σ=>∀ a,|((rawStartHubSet π d σ g a).card:ℝ)-t₀*Fintype.card U/d|<t) := by
  have hh := finiteLaw_common_event_lower (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS))
    (Finset.univ : Finset V)
    (fun a σ=>t≤|((rawStartHubSet π d σ g a).card:ℝ)-(∑ u,q u g/(d:ℝ))|)
    (fun _=>2*Real.exp (-2*t^2/Fintype.card U))
    (fun a _=>rawStartHubSet_tail π d hd q hq hQ s hs hS hnoshort g a t ht.le)
  simp only [hg,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.mem_univ,true_implies,not_le] at hh
  have hc : (Fintype.card U:ℝ)*(t₀/d)=t₀*Fintype.card U/d := by ring
  rw [hc] at hh
  convert hh using 1 <;> ring

end Oberwolfach
