module

public import Oberwolfach.ExponentialMarkedPhysicalCuts
public import Oberwolfach.ExponentialMarkedSpokeCuts
public import Oberwolfach.RawMarkedPotentialSampling
public import Oberwolfach.FiniteSumProduct
public import Oberwolfach.ProductGoodEvents

@[expose] public section

/-! Both physical rim cut families and both spoke cut families on a single
original marked outcome, with uniform exponential probability. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]

def MarkedReferenceCutFamilies (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ)
    (g : Γ) (j : Color) (α p k tstar : ℝ) (σ : RawMarkedOutcome V U Γ Color) : Prop :=
  (∀ b : Bool,∀ (X : Finset V) (Y : Finset U),
    1-tstar/8<(X.card:ℝ)/Fintype.card V+(Y.card:ℝ)/Fintype.card U →
    tstar/8*min ((Fintype.card U:ℝ)*X.card) ((Fintype.card V:ℝ)*Y.card)≤
      (bipartiteMatrixCut (fun v u=>if rawMarkedPairSpokes π d σ g j b v u then 1 else 0) X Y:ℝ)) ∧
  (∀ b : Bool,∀ δ : ℝ,δ≤α/32 → δ≤(if b then k else p)/32 → ∀ S T : Finset V,
    (1-2*δ)*Fintype.card V<(S.card:ℝ)+T.card →
    (α*(if b then k else p)/4)*Fintype.card V*min (S.card:ℝ) T.card≤
      (matrixCut (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) b) S T:ℝ))

def markedCutExponent (α kstar tstar ω : ℝ) (d : ℕ) : ℝ :=
  min (min (2*(2*kstar/32)^2) ((α*(2*kstar)^2/1024)^2/4))
    (min (2*(min (tstar/4) (tstar*ω/4))^2/(4*(d:ℝ)+3)^2)
      ((tstar^2*ω/128)^2/(4*(d:ℝ)+3)^2))

theorem markedCutExponent_pos (α kstar tstar ω : ℝ) (d : ℕ)
    (hα : 0<α) (hkstar : 0<kstar) (htstar : 0<tstar) (hω : 0<ω) :
    0<markedCutExponent α kstar tstar ω d := by
  unfold markedCutExponent
  positivity

theorem marked_reference_cut_event
    (α kstar tstar ω : ℝ) (hα : 0<α) (hα1 : α≤1/2)
    (hkstar : 0<kstar) (htstar : 0<tstar) (htstar1 : tstar≤1) (hω : 0<ω)
    (d : ℕ) (hd : 2≤d) :
    ∃ N : ℕ,1≤N ∧ ∀ (V U Γ Color : Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U],
      N≤Fintype.card V → ω*Fintype.card V≤(Fintype.card U:ℝ) → Fintype.card U≤Fintype.card V →
    ∀ P : SimpleGraph V,(∀ x,(1/2+α)*Fintype.card V≤(P.degree x:ℝ)) →
    ∀ (π : Equiv.Perm V),(∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1),kstar≤p → kstar≤k →
    ∀ (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (g : Γ) (j : Color) (s₀ t₀ : ℝ),(∀ u,q u g=t₀) → (∀ u,s u j=s₀) → tstar≤s₀ → tstar≤t₀ →
    1-36*Fintype.card V*Real.exp (-markedCutExponent α kstar tstar ω d*Fintype.card V)≤
    (FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS)).probability
      (MarkedReferenceCutFamilies P π d g j α p k tstar) := by
  obtain ⟨N₁,hN₁one,hN₁⟩ := rawMarked_spoke_cuts_exponential tstar ω htstar htstar1 hω d hd
  obtain ⟨N₂,hN₂one,hN₂⟩ := markedPhysical_large_cuts_exponential α kstar hα hα1 hkstar (3*d)
  refine ⟨max N₁ N₂,hN₁one.trans (le_max_left _ _),?_⟩
  intro V U Γ Color _ _ _ _ _ _ hnN hmlo hmhi P hP π hnoshort p k hp hk hsum hpmin hkmin q hq hQ s hs hS g j s₀ t₀ hg hj hslo htlo
  let n : ℝ := Fintype.card V
  let cR := min (2*(2*kstar/32)^2) ((α*(2*kstar)^2/1024)^2/4)
  let cH := min (2*(min (tstar/4) (tstar*ω/4))^2/(4*(d:ℝ)+3)^2)
    ((tstar^2*ω/128)^2/(4*(d:ℝ)+3)^2)
  let c := markedCutExponent α kstar tstar ω d
  have hn0 : 0≤n := Nat.cast_nonneg _
  let μ := FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)
  let ν := FiniteLaw.pi (fun _ : Sym2 V=>markedPhysicalLaw p k hp hk hsum)
  let E := fun σ : RawIntervalFamilyOutcome V U Γ Color=>∀ b : Bool,∀ (X : Finset V) (Y : Finset U),
    1-tstar/8<(X.card:ℝ)/Fintype.card V+(Y.card:ℝ)/Fintype.card U →
    tstar/8*min ((Fintype.card U:ℝ)*X.card) ((Fintype.card V:ℝ)*Y.card)≤
      (bipartiteMatrixCut (fun v u=>if rawMarkedSpokes π d σ g j b v u then 1 else 0) X Y:ℝ)
  let F := fun σ : Sym2 V→Option (Bool×Bool)=>∀ b : Bool,∀ δ : ℝ,δ≤α/32 → δ≤(if b then k else p)/32 →
    ∀ S T : Finset V,(1-2*δ)*Fintype.card V<(S.card:ℝ)+T.card →
    (α*(if b then k else p)/4)*Fintype.card V*min (S.card:ℝ) T.card≤
      (matrixCut (markedPhysicalRim P π (3*d) σ b) S T:ℝ)
  have hsp : 1-12*n*Real.exp (-cH*n)≤μ.probability E :=
    hN₁ V U Γ Color (by omega) hmlo hmhi π q hq hQ s hs hS g j s₀ t₀ hg hj hslo htlo hnoshort
  have hph : 1-24*n*Real.exp (-cR*n)≤ν.probability F :=
    hN₂ V (by omega) P hP π p k hp hk hsum hpmin hkmin
  have hjoint := finiteLaw_product_good_lower μ ν E (fun _ σ=>F σ)
    (12*n*Real.exp (-cH*n)) (24*n*Real.exp (-cR*n)) (by positivity) hsp (fun _ _=>hph)
  have heq : (FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS)).probability
      (MarkedReferenceCutFamilies P π d g j α p k tstar)=
      (μ.prod ν).probability (fun z=>E z.1 ∧ F z.2) :=
    finiteLaw_pi_sum_probability (rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS)
      (fun σ τ=>E σ ∧ F τ)
  rw [heq]
  have heR : Real.exp (-cR*n)≤Real.exp (-c*n) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right (min_le_left cR cH) hn0
    change c*n≤cR*n at hh
    linarith only [hh]
  have heH : Real.exp (-cH*n)≤Real.exp (-c*n) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right (min_le_right cR cH) hn0
    change c*n≤cH*n at hh
    linarith only [hh]
  have hbR := mul_le_mul_of_nonneg_left heR (show 0≤24*n by positivity)
  have hbH := mul_le_mul_of_nonneg_left heH (show 0≤12*n by positivity)
  apply le_trans _ hjoint
  change 1-36*n*Real.exp (-c*n)≤_
  linarith only [hbR,hbH]

end Oberwolfach
