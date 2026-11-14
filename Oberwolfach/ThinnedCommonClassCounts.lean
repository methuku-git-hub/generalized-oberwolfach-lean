module

public import Oberwolfach.SupportedIndicatorCounts
public import Oberwolfach.ThinnedMarkedCoordinates

@[expose] public section

/-! Common classes sampled with the same coins as the common weights.
All test domains are fixed before sampling, and may include neighbours of
vertices outside the domain. No independence of the vertex indicators is
assumed: their primitive supports overlap in a bounded number of places. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def thinnedCommonClassCount (π : Equiv.Perm V) (d : ℕ) (g : Γ) (j : Color) (u u' : U)
    (b : Bool) (T : Finset V) (σ : ThinnedMarkedOutcome V U Γ Color) : ℝ :=
  supportedIndicatorCount T (fun τ x=>decide (thinnedMarkedSpokes π d g j u u' τ b x ())) σ

theorem thinnedCommonClassCount_card (π : Equiv.Perm V) (d : ℕ) (g : Γ) (j : Color) (u u' : U)
    (b : Bool) (T : Finset V) (σ : ThinnedMarkedOutcome V U Γ Color) :
    thinnedCommonClassCount π d g j u u' b T σ=
      ((T.filter (fun x=>thinnedMarkedSpokes π d g j u u' σ b x ())).card:ℝ) := by
  unfold thinnedCommonClassCount supportedIndicatorCount
  simp only [decide_eq_true_eq]
  rw [← Finset.sum_filter]
  simp

theorem thinnedCommonClass_supported (π : Equiv.Perm V) (d : ℕ) (g : Γ) (j : Color) (u u' : U)
    (b : Bool) (x : V) (σ τ : ThinnedMarkedOutcome V U Γ Color)
    (h : ∀ e∈thinnedMarkedResourceCoordinates π d u u' (Sum.inr (b,x,())),σ e=τ e) :
    decide (thinnedMarkedSpokes π d g j u u' σ b x ())=
      decide (thinnedMarkedSpokes π d g j u u' τ b x ()) := by
  exact thinnedMarkedResourceState_supported (⊥ : SimpleGraph V) π d g j u u' (Sum.inr (b,x,())) σ τ h

theorem thinnedCommonClass_reverse_card (π : Equiv.Perm V) (d : ℕ) (u u' : U)
    (b : Bool) (e : RawWheelCoordinate V U⊕V) :
    (Finset.univ.filter (fun x : V=>e∈thinnedMarkedResourceCoordinates π d u u' (Sum.inr (b,x,())))).card≤16*d+14 := by
  apply le_trans _ (thinnedMarkedResourceCoordinates_reverse_card π d u u' e)
  apply Finset.card_le_card_of_injOn (fun x : V=>Sum.inr (b,x,()))
  · intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hx).2⟩
  · intro x hx y hy h
    exact congrArg (fun a : Bool×V×Unit=>a.2.1) (Sum.inr.inj h)

attribute [local irreducible] thinnedMarkedResourceCoordinates

theorem thinnedCommonClassCount_mean_tail
    (μ : ∀ e : RawWheelCoordinate V U⊕V,FiniteLaw (ThinnedMarkedCoordinateState Γ Color e))
    (π : Equiv.Perm V) (d : ℕ) (g : Γ) (j : Color) (u u' : U)
    (b : Bool) (T : Finset V) (hn : 0<Fintype.card V) (t : ℝ) (ht : 0<t) :
    (FiniteLaw.pi μ).probability (fun σ=>t≤|thinnedCommonClassCount π d g j u u' b T σ-
      (FiniteLaw.pi μ).expectation (thinnedCommonClassCount π d g j u u' b T)|)≤
      2*Real.exp (-2*t^2/((16*(d:ℝ)+14)^2*Fintype.card V)) := by
  letI : DecidableEq V := Classical.decEq _
  have hread (x : V) : ((thinnedMarkedResourceCoordinates π d u u' (Sum.inr (b,x,()))).card:ℝ)≤16*(d:ℝ)+14 := by
    have hh := Nat.cast_le (α:=ℝ).mpr (thinnedMarkedResourceCoordinates_card π d u u' (Sum.inr (b,x,())))
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hh
  have hreverse (e : RawWheelCoordinate V U⊕V) :
      ((Finset.univ.filter (fun x : V=>e∈thinnedMarkedResourceCoordinates π d u u' (Sum.inr (b,x,())))).card:ℝ)≤16*(d:ℝ)+14 := by
    have hh := Nat.cast_le (α:=ℝ).mpr (thinnedCommonClass_reverse_card π d u u' b e)
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hh
  have hh := supportedIndicatorCount_tail μ T
    (fun x=>thinnedMarkedResourceCoordinates π d u u' (Sum.inr (b,x,())))
    (fun σ x=>decide (thinnedMarkedSpokes π d g j u u' σ b x ()))
    (fun x σ τ h=>thinnedCommonClass_supported π d g j u u' b x σ τ h)
    (16*(d:ℝ)+14) (by positivity) hn
    hread (by intro e;convert hreverse e using 1 <;> congr!) t ht
  convert hh using 1 <;> congr!

section Sampling
variable (π : Equiv.Perm V)
    (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hphys : 2*p+2*k≤1) (d : ℕ) (hd : 2≤d)
    (q : U→Γ→ℝ) (hq : ∀ u a,0≤q u a) (hQ : ∀ u,∑ a,q u a≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a))
    (hnoshort : ∀ x l,0<l → l<2*d+1 → (π^l) x≠x)
    (θ : ℝ) (hθ : 0≤θ) (hθ1 : θ≤1) (g : Γ) (j : Color) (u u' : U) (hu : u≠u')

local notation "μ" => thinnedMarkedLaw (rawMarkedWheelLaw p k hp hk hphys d hd q hq hQ s hs hS) θ hθ hθ1

include hnoshort hu in
theorem thinnedCommonClassCount_expectation (b : Bool) (T : Finset V) :
    (FiniteLaw.pi μ).expectation (thinnedCommonClassCount π d g j u u' b T)=
      (if b then q u g*q u' g else s u j*s u' j*θ)*T.card := by
  unfold thinnedCommonClassCount
  rw [supportedIndicatorCount_expectation]
  simp only [decide_eq_true_eq]
  simp_rw [thinnedMarked_spoke_probability (⊥ : SimpleGraph V) π p k hp hk hphys d hd q hq hQ s hs hS
    hnoshort θ hθ hθ1 g j u u' hu]
  simp [mul_comm]

include hnoshort hu in
theorem thinnedCommonClassCount_tail (b : Bool) (T : Finset V) (hn : 0<Fintype.card V)
    (t : ℝ) (ht : 0<t) :
    (FiniteLaw.pi μ).probability (fun σ=>t≤
      |thinnedCommonClassCount π d g j u u' b T σ-
        (if b then q u g*q u' g else s u j*s u' j*θ)*T.card|)≤
      2*Real.exp (-2*t^2/((16*(d:ℝ)+14)^2*Fintype.card V)) := by
  have hh := thinnedCommonClassCount_mean_tail μ π d g j u u' b T hn t ht
  change (FiniteLaw.pi μ).probability (fun σ=>t≤
    |thinnedCommonClassCount π d g j u u' b T σ-
      (FiniteLaw.pi μ).expectation (thinnedCommonClassCount π d g j u u' b T)|)≤_ at hh
  rw [thinnedCommonClassCount_expectation π p k hp hk hphys d hd q hq hQ s hs hS hnoshort θ hθ hθ1 g j u u' hu] at hh
  exact hh

include hnoshort hu in
theorem thinnedCommonClassCount_common_event {I : Type} [Fintype I] (T : I→Finset V)
    (hn : 0<Fintype.card V) (t : ℝ) (ht : 0<t) :
    1-(2*Fintype.card I:ℝ)*(2*Real.exp (-2*t^2/((16*(d:ℝ)+14)^2*Fintype.card V)))≤
      (FiniteLaw.pi μ).probability (fun σ=>∀ b i,
        |thinnedCommonClassCount π d g j u u' b (T i) σ-
          (if b then q u g*q u' g else s u j*s u' j*θ)*(T i).card|<t) := by
  have hh := finiteLaw_common_event_lower (FiniteLaw.pi μ) (Finset.univ : Finset (Bool×I))
    (fun a σ=>t≤|thinnedCommonClassCount π d g j u u' a.1 (T a.2) σ-
      (if a.1 then q u g*q u' g else s u j*s u' j*θ)*(T a.2).card|)
    (fun _=>2*Real.exp (-2*t^2/((16*(d:ℝ)+14)^2*Fintype.card V)))
    (fun a _=>thinnedCommonClassCount_tail π p k hp hk hphys d hd q hq hQ s hs hS hnoshort θ hθ hθ1 g j u u' hu a.1 (T a.2) hn t ht)
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.mem_univ,true_implies,not_le,
    Fintype.card_prod,Fintype.card_bool,Nat.cast_mul,Nat.cast_ofNat,Prod.forall] using hh
end Sampling
end Oberwolfach
