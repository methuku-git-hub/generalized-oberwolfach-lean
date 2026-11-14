module

public import Oberwolfach.RawMarkedBaseCycles
public import Oberwolfach.ExponentialMarkedFirstEvent
public import Oberwolfach.ExponentialMarkedPath

@[expose] public section

/-! One raw-sample event for every pair of row roots, every pair of hubs,
and both common-path types. The row roots are distinct but need not be
separated. All four root spokes remain omitted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def markedPathExponent (r : ℕ) (α sstar tstar kstar ω : ℝ) (d : ℕ) : ℝ :=
  min (markedFirstExponent (r+4) α sstar tstar ω d)
    (2*(kstar^(r+7)*(α*(min sstar tstar)^2/8)^(r+4)/2)^2/(2*((r:ℝ)+4)*((r:ℝ)+7)))

theorem markedPathExponent_pos (r : ℕ) (α sstar tstar kstar ω : ℝ) (d : ℕ)
    (hα : 0<α) (hsstar : 0<sstar) (htstar : 0<tstar) (hkstar : 0<kstar) (hω : 0<ω) :
    0<markedPathExponent r α sstar tstar kstar ω d := by
  apply lt_min (markedFirstExponent_pos (r+4) α sstar tstar ω d hα hsstar htstar hω)
  positivity

theorem rawMarked_paths_exponential_event
    (r : ℕ) (hr : 1≤r) (α sstar tstar kstar ω : ℝ) (hα : 0<α) (hα1 : α≤1/2)
    (hsstar : 0<sstar) (htstar : 0<tstar) (hkstar : 0<kstar) (hω : 0<ω)
    (d : ℕ) (hd : 2≤d) :
    ∃ N : ℕ,∀ (V U Γ Color : Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U],
      N≤Fintype.card V → ω*Fintype.card V≤(Fintype.card U:ℝ) → Fintype.card U≤Fintype.card V →
    ∀ P : SimpleGraph V,(∀ x,(1/2+α)*Fintype.card V≤(P.degree x:ℝ)) →
    ∀ (π : Equiv.Perm V),(∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1),kstar≤p → kstar≤k →
    ∀ (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (g : Γ) (j₀ : Color) (s₀ t₀ : ℝ),(∀ u,q u g=t₀) → (∀ u,s u j₀=s₀) → sstar≤s₀ → tstar≤t₀ →
    let μ := (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).prod
      (FiniteLaw.pi (fun _ : Sym2 V=>markedPhysicalLaw p k hp hk hsum))
    1-18*(Fintype.card V:ℝ)^(r+8)*Real.exp (-markedPathExponent r α sstar tstar kstar ω d*Fintype.card V)≤μ.probability (fun z=>
      ∀ v v' : V,v≠v' → ∀ u : Fin 2→U,Function.Injective u → ∀ j : Bool,
        let T := rawMarkedPairClass π d z.1 g j₀ u
        (kstar^(r+7)*(α*(min sstar tstar)^2/8)^(r+4)/2)*(Fintype.card V:ℝ)^(r+4)≤
          (Fintype.card {C : DenseRootMarkedPathFamily P π (3*d) (r+3) j (T false) (T true) v v' //
            MarkedPathRims P π (3*d) (r+3) j v v' z.2 C.val}:ℝ)) := by
  let θ := (min sstar tstar)^2/2
  have hθ : 0<θ := by dsimp [θ];positivity
  obtain ⟨N₂,hN₂⟩ := markedPath_exponential_event r (3*d) (by omega) hr α θ kstar hα
    (by linarith only [hα1]) hθ hkstar 4
  refine ⟨max 1 N₂,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hnN hmlo hmhi P hP π hnoshort p k hp hk hsum hpmin hkmin q hq hQ s hs hS g j₀ s₀ t₀ hg hj hslo htlo
  let n := Fintype.card V
  have hn : 0<n := by dsimp [n];omega
  let μ := FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)
  let ν := FiniteLaw.pi (fun _ : Sym2 V=>markedPhysicalLaw p k hp hk hsum)
  let R := {v : Fin 2→V // Function.Injective v}
  let H := {u : Fin 2→U // Function.Injective u}
  let J := Bool×R×H
  have hR : Fintype.card R≤n^2 := by
    have hh := Fintype.card_subtype_le (Function.Injective (α:=Fin 2) (β:=V))
    simpa only [Fintype.card_fun,Fintype.card_fin] using hh
  have hH : Fintype.card H≤n^2 := by
    have hh := Fintype.card_subtype_le (Function.Injective (α:=Fin 2) (β:=U))
    simp only [Fintype.card_fun,Fintype.card_fin] at hh
    exact hh.trans (Nat.pow_le_pow_left hmhi 2)
  have hJ : Fintype.card J≤2*n^4 := by
    change Fintype.card (Bool×R×H)≤_
    simp only [Fintype.card_prod,Fintype.card_bool]
    calc
      _ ≤ 2*(n^2*n^2) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hR hH)
      _ = _ := by ring
  let E := fun σ : RawIntervalFamilyOutcome V U Γ Color=>
    ∀ u : Fin 2→U,Function.Injective u →
      let T := rawMarkedPairClass π d σ g j₀ u
      ∀ b : Bool,(θ*Fintype.card V≤((T b).card:ℝ)) ∧
        (∀ x : V,(1/2+α/2)*(T b).card≤((P.neighborFinset x∩T b).card:ℝ)) ∧
        (∀ x : V,(1/2+α/2)*(T b).card≤((P.neighborFinset x∩(T b).image π).card:ℝ))
  let A := fun (σ : RawIntervalFamilyOutcome V U Γ Color) (τ : Sym2 V→Option (Bool×Bool))=>
    ∀ a : J,
      (kstar^(r+7)*(α*θ/4)^(r+4)/2)*(n:ℝ)^(r+4)≤
        (Fintype.card {C : DenseRootMarkedPathFamily P π (3*d) (r+3) a.1
          (rawMarkedPairClass π d σ g j₀ a.2.2.val false) (rawMarkedPairClass π d σ g j₀ a.2.2.val true)
          (a.2.1.val 0) (a.2.1.val 1) //
            MarkedPathRims P π (3*d) (r+3) a.1 (a.2.1.val 0) (a.2.1.val 1) τ C.val}:ℝ)
  let cF := markedFirstExponent (r+4) α sstar tstar ω d
  let cR := 2*(kstar^(r+7)*(α*θ/4)^(r+4)/2)^2/(2*((r:ℝ)+4)*((r:ℝ)+7))
  let errF := 14*(n:ℝ)^(r+4+4)*Real.exp (-cF*n)
  let errR := 4*(n:ℝ)^4*Real.exp (-cR*n)
  have hfirst : 1-errF≤μ.probability E := by
    apply (rawMarked_first_exponential_event (r+4) α sstar tstar ω hα hα1 hsstar htstar hω d hd V U Γ Color hn hmlo hmhi P hP π q hq hQ s hs hS g j₀ s₀ t₀ hg hj hslo htlo hnoshort).trans
    apply finiteLaw_probability_mono
    intro σ hσ u hu
    exact (hσ.2 u hu).2.2
  have hsecond (σ : RawIntervalFamilyOutcome V U Γ Color) (hσ : E σ) :
      1-errR≤ν.probability (A σ) := by
    apply hN₂ V J (by omega) hJ P π
      (fun a=>rawMarkedPairClass π d σ g j₀ a.2.2.val false)
      (fun a=>rawMarkedPairClass π d σ g j₀ a.2.2.val true)
      (fun a=>a.1) (fun a=>a.2.1.val 0) (fun a=>a.2.1.val 1)
    · intro a he
      have hh := a.2.1.property he
      exact (show (0:Fin 2)≠1 by decide) hh
    · intro a;exact (hσ a.2.2.val a.2.2.property false).1
    · intro a;exact (hσ a.2.2.val a.2.2.property true).1
    · intro a;exact (hσ a.2.2.val a.2.2.property false).2.1
    · intro a;exact (hσ a.2.2.val a.2.2.property true).2.2
    · exact hpmin
    · exact hkmin
  have hjoint := finiteLaw_product_good_lower μ ν E A errF errR (by dsimp [errR];positivity) hfirst hsecond
  have he : α*θ/4=α*(min sstar tstar)^2/8 := by dsimp [θ];ring
  have hsum := two_polynomial_exponential_errors_le (n:ℝ) 14 4 cF cR (r+4+4) 4 (r+8)
    (by exact_mod_cast hn) (by norm_num) (by norm_num) (by omega) (by omega)
  have hbound : 1-18*(n:ℝ)^(r+8)*Real.exp (-markedPathExponent r α sstar tstar kstar ω d*n)≤1-errF-errR := by
    have hc : min cF cR=markedPathExponent r α sstar tstar kstar ω d := by dsimp [cF,cR,markedPathExponent];rw [he]
    rw [hc] at hsum
    change errF+errR≤(14+4)*(n:ℝ)^(r+8)*Real.exp (-markedPathExponent r α sstar tstar kstar ω d*n) at hsum
    linarith only [hsum]
  apply (hbound.trans hjoint).trans
  apply finiteLaw_probability_mono
  intro z hz v v' hvv u hu j
  have hv : Function.Injective (![v,v'] : Fin 2→V) := by
    intro a c he;fin_cases a <;> fin_cases c <;> simp_all
  have hh := hz.2 (j,⟨![v,v'],hv⟩,⟨u,hu⟩)

  simpa only [he,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one] using hh

end Oberwolfach
