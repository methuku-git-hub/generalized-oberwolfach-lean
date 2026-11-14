module

public import Oberwolfach.MarkedRimUniformCapacity
public import Oberwolfach.RawMarkedSpokeReference
public import Oberwolfach.RawMarkedPotentialSampling
public import Oberwolfach.FiniteSumProduct
public import Oberwolfach.ProductGoodEvents

@[expose] public section

/-! Reference degrees and intersections in one original marked sample.
These predicates state the actual counts; they impose no independence
between tests and do not change any marginal array after exposure. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def MarkedReferenceStatistics (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ)
    (g : Γ) (j : Color) (D ε δ γ p k s₀ t₀ : ℝ) (σ : RawMarkedOutcome V U Γ Color) : Prop :=
  ((∀ a x,
    |((∑ y,markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) a x y:ℕ):ℝ)-(if a then k else p)*D|≤ε*Fintype.card V ∧
    |((∑ y,markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) a y x:ℕ):ℝ)-(if a then k else p)*D|≤ε*Fintype.card V) ∧
    ∀ x y,x≠y →3/2*γ*p^2*Fintype.card V≤
      ((Finset.univ.filter (fun z=>0<markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) false x z ∧
        0<markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) false z y)).card:ℝ)) ∧
  ((∀ r : ℕ,1≤r → r≤3 → ∀ (b : Bool) (u : Fin r→U),Function.Injective u →
    |((Finset.univ.filter (fun v=>∀ i,rawMarkedPairSpokes π d σ g j b v (u i))).card:ℝ)-
      (if b then t₀ else s₀)^r*Fintype.card V|≤δ*Fintype.card V) ∧
    ∀ (b : Bool) (x y : V),¬PermutationClose π (3*d) x y →
    |(Fintype.card U:ℝ)⁻¹*(∑ u : U,(if b then t₀ else s₀)⁻¹^2*
      (if rawMarkedPairSpokes π d σ g j b x u ∧ rawMarkedPairSpokes π d σ g j b y u then (1:ℝ) else 0))-1|≤δ)

def markedReferenceExponent (ε δ γ pstar sstar κ : ℝ) (d : ℕ) : ℝ :=
  min (min (ε^2/2) (γ^2*pstar^4/16))
    (min (2*δ^2/(3*(4*(d:ℝ)+3)^2)) (δ^2*sstar^4*κ/(4*(d:ℝ)+3)^2))

theorem markedReferenceExponent_pos (ε δ γ pstar sstar κ : ℝ) (d : ℕ)
    (hε : 0<ε) (hδ : 0<δ) (hγ : 0<γ) (hpstar : 0<pstar) (hsstar : 0<sstar) (hκ : 0<κ) :
    0<markedReferenceExponent ε δ γ pstar sstar κ d := by
  unfold markedReferenceExponent
  positivity

theorem marked_reference_statistics
    (ε δ γ pstar sstar κ : ℝ) (hε : 0<ε) (hδ : 0<δ) (hγ : 0<γ)
    (hpstar : 0<pstar) (hsstar : 0<sstar) (hκ : 0<κ) (d : ℕ) (hd : 2≤d) :
    ∃ N : ℕ,∀ (V U Γ Color : Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U],
      N≤Fintype.card V → κ*Fintype.card V≤(Fintype.card U:ℝ) → Fintype.card U≤Fintype.card V →
    ∀ (P : SimpleGraph V) (π : Equiv.Perm V),
      (∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1),pstar≤p →
    ∀ D δP : ℝ,0≤δP → δP≤ε/4 →
      (∀ x,|(P.degree x:ℝ)-D|≤δP*Fintype.card V) →
      (∀ x,(1/2+γ)*Fintype.card V≤(P.degree x:ℝ)) →
    ∀ (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (g : Γ) (j : Color) (s₀ t₀ : ℝ),(∀ u,q u g=t₀) → (∀ u,s u j=s₀) → sstar≤s₀ → sstar≤t₀ →
    1-36*(Fintype.card V:ℝ)^3*Real.exp (-markedReferenceExponent ε δ γ pstar sstar κ d*Fintype.card V)≤
    (FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS)).probability
      (MarkedReferenceStatistics P π d g j D ε δ γ p k s₀ t₀) := by
  obtain ⟨N,hN⟩ := markedPhysicalRim_uniform_capacity_event ε γ pstar hε hγ hpstar (3*d)
  refine ⟨max 1 N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hnN hmlo hmhi P π hnoshort p k hp hk hsum hlo D δP hδP hδε hPreg hP q hq hQ s hs hS g j s₀ t₀ hg hj hslo htlo
  let n : ℝ := Fintype.card V
  let cR := min (ε^2/2) (γ^2*pstar^4/16)
  let cH := min (2*δ^2/(3*(4*(d:ℝ)+3)^2)) (δ^2*sstar^4*κ/(4*(d:ℝ)+3)^2)
  let c := markedReferenceExponent ε δ γ pstar sstar κ d
  have hn1 : 1≤n := by dsimp [n];exact_mod_cast (show 1≤Fintype.card V by omega)
  have hn0 : 0<n := by linarith
  let μ := FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)
  let ν := FiniteLaw.pi (fun _ : Sym2 V=>markedPhysicalLaw p k hp hk hsum)
  let Rim := fun σ : Sym2 V→Option (Bool×Bool)=>
    (∀ a x,
      |((∑ y,markedPhysicalRim P π (3*d) σ a x y:ℕ):ℝ)-(if a then k else p)*D|≤ε*Fintype.card V ∧
      |((∑ y,markedPhysicalRim P π (3*d) σ a y x:ℕ):ℝ)-(if a then k else p)*D|≤ε*Fintype.card V) ∧
    ∀ x y,x≠y →3/2*γ*p^2*Fintype.card V≤
      ((Finset.univ.filter (fun z=>0<markedPhysicalRim P π (3*d) σ false x z ∧
        0<markedPhysicalRim P π (3*d) σ false z y)).card:ℝ)
  let Spoke := fun σ : RawIntervalFamilyOutcome V U Γ Color=>
    (∀ r : ℕ,1≤r → r≤3 → ∀ (b : Bool) (u : Fin r→U),Function.Injective u →
      |((Finset.univ.filter (fun v=>∀ i,rawMarkedSpokes π d σ g j b v (u i))).card:ℝ)-
        (if b then t₀ else s₀)^r*Fintype.card V|≤δ*Fintype.card V) ∧
    ∀ (b : Bool) (x y : V),¬PermutationClose π (3*d) x y →
      |(Fintype.card U:ℝ)⁻¹*(∑ u : U,(if b then t₀ else s₀)⁻¹^2*
        (if rawMarkedSpokes π d σ g j b x u ∧ rawMarkedSpokes π d σ g j b y u then (1:ℝ) else 0))-1|≤δ
  have hR : 1-20*n^2*Real.exp (-cR*n)≤ν.probability Rim :=
    hN V (by omega) P π p k hp hk hsum hlo D δP hδP hδε hPreg hP
  have hH : 1-16*n^3*Real.exp (-cH*n)≤μ.probability Spoke :=
    rawMarked_spoke_reference_event π d hd q hq hQ s hs hS hnoshort (by omega) κ hκ hmlo hmhi
      g j s₀ t₀ hg hj δ sstar hδ hsstar hslo htlo
  have hjoint := finiteLaw_product_good_lower μ ν Spoke (fun _ σ=>Rim σ)
    (16*n^3*Real.exp (-cH*n)) (20*n^2*Real.exp (-cR*n)) (by positivity) hH (fun _ _=>hR)
  have heq : (FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS)).probability
      (MarkedReferenceStatistics P π d g j D ε δ γ p k s₀ t₀)=
      (μ.prod ν).probability (fun z=>Rim z.2 ∧ Spoke z.1) := by
    exact finiteLaw_pi_sum_probability (rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS)
      (fun σ τ=>Rim τ ∧ Spoke σ)
  rw [heq]
  have heR : Real.exp (-cR*n)≤Real.exp (-c*n) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right (min_le_left cR cH) hn0.le
    change c*n≤cR*n at hh
    linarith only [hh]
  have heH : Real.exp (-cH*n)≤Real.exp (-c*n) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right (min_le_right cR cH) hn0.le
    change c*n≤cH*n at hh
    linarith only [hh]
  have hpow : n^2≤n^3 := by nlinarith only [mul_nonneg (sq_nonneg n) (sub_nonneg.mpr hn1)]
  have hbR : 20*n^2*Real.exp (-cR*n)≤20*n^3*Real.exp (-c*n) :=
    mul_le_mul (by linarith only [hpow]) heR (by positivity) (by positivity)
  have hbH : 16*n^3*Real.exp (-cH*n)≤16*n^3*Real.exp (-c*n) :=
    mul_le_mul_of_nonneg_left heH (by positivity)
  have hbound : 1-36*n^3*Real.exp (-c*n)≤1-16*n^3*Real.exp (-cH*n)-20*n^2*Real.exp (-cR*n) := by
    linarith only [hbR,hbH]
  apply (hbound.trans hjoint).trans
  exact finiteLaw_probability_mono _ _ _ (fun _ h=>h.symm)

end Oberwolfach
