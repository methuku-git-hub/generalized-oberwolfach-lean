module

public import Oberwolfach.RawMarkedSmallIntersections
public import Oberwolfach.RawMarkedCodegreeTails
public import Oberwolfach.GoodPlacementEvents

@[expose] public section

/-! The marked reference spoke estimates on one original interval sample:
degrees, intersections of two or three distinct hub neighbourhoods, and
normalized codegrees at all nonexceptional label pairs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U]

theorem rawMarked_spoke_reference_event
    (π : Equiv.Perm V) (d : ℕ) (hd : 2≤d)
    (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort : ∀ x l,0<l → l<2*d+1 → (π^l) x≠x)
    (hn : 1≤Fintype.card V) (κ : ℝ) (hκ : 0<κ)
    (hmlo : κ*Fintype.card V≤(Fintype.card U:ℝ)) (hmhi : Fintype.card U≤Fintype.card V)
    (g : Γ) (j : Color) (s₀ t₀ : ℝ) (hg : ∀ u,q u g=t₀) (hj : ∀ u,s u j=s₀)
    (δ sstar : ℝ) (hδ : 0<δ) (hsstar : 0<sstar) (hslo : sstar≤s₀) (htlo : sstar≤t₀) :
    1-16*(Fintype.card V:ℝ)^3*Real.exp
      (-min (2*δ^2/(3*(4*(d:ℝ)+3)^2)) (δ^2*sstar^4*κ/(4*(d:ℝ)+3)^2)*Fintype.card V)≤
    (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability
      (fun σ=>(∀ k : ℕ,1≤k → k≤3 → ∀ (b : Bool) (u : Fin k→U),Function.Injective u →
        |((Finset.univ.filter (fun v=>∀ i,rawMarkedSpokes π d σ g j b v (u i))).card:ℝ)-
          (if b then t₀ else s₀)^k*Fintype.card V|≤δ*Fintype.card V) ∧
        ∀ (b : Bool) (x y : V),¬PermutationClose π (3*d) x y →
        |(Fintype.card U:ℝ)⁻¹*(∑ u : U,(if b then t₀ else s₀)⁻¹^2*
          (if rawMarkedSpokes π d σ g j b x u ∧ rawMarkedSpokes π d σ g j b y u then (1:ℝ) else 0))-1|≤δ) := by
  let n : ℝ := Fintype.card V
  let m : ℝ := Fintype.card U
  let A : ℝ := 4*d+3
  let c₁ : ℝ := 2*δ^2/(3*A^2)
  let c₂ : ℝ := δ^2*sstar^4*κ/A^2
  let c := min c₁ c₂
  have hn1 : 1≤n := by dsimp [n];exact_mod_cast hn
  have hn0 : 0<n := by linarith
  have hm0 : 0<m := (show 0<κ*n by positivity).trans_le hmlo
  have hmnat : 0<Fintype.card U := by
    have hm0' : (0:ℝ)<Fintype.card U := hm0
    exact_mod_cast hm0'
  have hmle : m≤n := by dsimp [m,n];exact_mod_cast hmhi
  have hA : 0<A := by dsimp [A];positivity
  let μ := FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)
  have hI := rawMarkedSmallIntersections_event π d hd q hq hQ s hs hS hnoshort
    (by omega : 0<Fintype.card V) (by omega : 1≤Fintype.card U) g j s₀ t₀ hg hj 3 (by omega) (δ*n) (by positivity)
  have hC := rawMarkedCodegree_normalized_event π d hd q hq hQ s hs hS hnoshort hmnat
    g j s₀ t₀ hg hj δ sstar hδ hsstar hslo htlo
  have hI' : 1-12*m^3*Real.exp (-2*(δ*n)^2/(A^2*(3*n)))≤
      μ.probability (fun σ=>∀ k : ℕ,1≤k → k≤3 → ∀ (b : Bool) (u : Fin k→U),Function.Injective u →
        |((Finset.univ.filter (fun v=>∀ i,rawMarkedSpokes π d σ g j b v (u i))).card:ℝ)-
          (if b then t₀ else s₀)^k*Fintype.card V|≤δ*n) := by
    have hI'' : 1-12*m^3*Real.exp (-2*(δ*n)^2/(A^2*(3*n)))≤
        μ.probability (fun σ=>∀ k : ℕ,1≤k → k≤3 → ∀ (b : Bool) (u : Fin k→U),Function.Injective u →
          |((Finset.univ.filter (fun v=>∀ i,rawMarkedSpokes π d σ g j b v (u i))).card:ℝ)-
            (if b then t₀ else s₀)^k*Fintype.card V|<δ*n) := by
      convert hI using 1 <;> norm_num [m,n,A]
    apply hI''.trans
    apply finiteLaw_probability_mono
    intro σ hσ k hk hk' b u hu
    exact (hσ k hk hk' b u hu).le
  have hjoint := finiteLaw_good_intersection μ
    (fun σ=>∀ k : ℕ,1≤k → k≤3 → ∀ (b : Bool) (u : Fin k→U),Function.Injective u →
      |((Finset.univ.filter (fun v=>∀ i,rawMarkedSpokes π d σ g j b v (u i))).card:ℝ)-
        (if b then t₀ else s₀)^k*Fintype.card V|≤δ*n) _
    (4*n^2*Real.exp (-2*(δ*sstar^2*m)^2/(A^2*(2*m)))) hC
  have hbase := (sub_le_sub_right hI' (4*n^2*Real.exp (-2*(δ*sstar^2*m)^2/(A^2*(2*m))))).trans hjoint
  have heI : -2*(δ*n)^2/(A^2*(3*n)) = -c₁*n := by dsimp [c₁];field_simp [ne_of_gt hn0,ne_of_gt hA] <;> ring
  have heC : -2*(δ*sstar^2*m)^2/(A^2*(2*m))=-(δ^2*sstar^4/A^2)*m := by field_simp [ne_of_gt hm0,ne_of_gt hA] <;> ring
  have hexpI : Real.exp (-c₁*n)≤Real.exp (-c*n) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right (min_le_left c₁ c₂) hn0.le
    linarith only [hh]
  have hexpC : Real.exp (-(δ^2*sstar^4/A^2)*m)≤Real.exp (-c*n) := by
    apply Real.exp_le_exp.mpr
    have h1 := mul_le_mul_of_nonneg_left hmlo (show 0≤δ^2*sstar^4/A^2 by positivity)
    have h2 := mul_le_mul_of_nonneg_right (min_le_right c₁ c₂) hn0.le
    change c*n≤δ^2*sstar^4*κ/A^2*n at h2
    change (δ^2*sstar^4/A^2)*(κ*n)≤(δ^2*sstar^4/A^2)*m at h1
    have he : δ^2*sstar^4*κ/A^2*n=(δ^2*sstar^4/A^2)*(κ*n) := by ring
    rw [he] at h2
    linarith only [h1,h2]
  have hpow : n^2≤n^3 := by nlinarith only [mul_nonneg (sq_nonneg n) (sub_nonneg.mpr hn1)]
  have hbI : 12*m^3*Real.exp (-2*(δ*n)^2/(A^2*(3*n)))≤12*n^3*Real.exp (-c*n) := by
    rw [heI]
    apply mul_le_mul _ hexpI (by positivity) (by positivity)
    gcongr
  have hbC : 4*n^2*Real.exp (-2*(δ*sstar^2*m)^2/(A^2*(2*m)))≤4*n^3*Real.exp (-c*n) := by
    rw [heC]
    exact mul_le_mul (by linarith only [hpow]) hexpC (by positivity) (by positivity)
  apply le_trans _ hbase
  change 1-16*n^3*Real.exp (-c*n)≤_
  linarith only [hbI,hbC]

end Oberwolfach
