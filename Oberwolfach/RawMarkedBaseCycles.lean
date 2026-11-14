module

public import Oberwolfach.MarkedBaseUniformEvent
public import Oberwolfach.RawMarkedFirstEvent
public import Oberwolfach.ProductGoodEvents

@[expose] public section

/-! Compatible hubs and actual common base cycles in the original two
exposures. All hub pairs use one physical outcome. The lower coefficients
are fixed before d and before the host or feasible arrays are supplied. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def rawMarkedPairClass {V U Γ Color : Type} [Fintype V] [DecidableEq V]
    (π : Equiv.Perm V) (d : ℕ) (σ : RawIntervalFamilyOutcome V U Γ Color)
    (g : Γ) (j : Color) (u : Fin 2→U) (b : Bool) : Finset V :=
  Finset.univ.filter (fun v=>∀ i,rawMarkedSpokes π d σ g j b v (u i))

theorem rawMarked_base_cycles_event
    (m : ℕ) (hm : 2≤m) (α sstar tstar kstar ω : ℝ) (hα : 0<α) (hα1 : α≤1/2)
    (hsstar : 0<sstar) (htstar : 0<tstar) (hkstar : 0<kstar) (hω : 0<ω)
    (d q₀ : ℕ) (hd : 2≤d) :
    ∃ N : ℕ,∀ (V U Γ Color : Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U],
      N≤Fintype.card V → ω*Fintype.card V≤(Fintype.card U:ℝ) → Fintype.card U≤Fintype.card V →
    ∀ P : SimpleGraph V,(∀ x,(1/2+α)*Fintype.card V≤(P.degree x:ℝ)) →
    ∀ (π : Equiv.Perm V),(∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1),kstar≤p → kstar≤k →
    ∀ (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (g : Γ) (j : Color) (s₀ t₀ : ℝ),(∀ u,q u g=t₀) → (∀ u,s u j=s₀) → sstar≤s₀ → tstar≤t₀ →
    let μ := (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).prod
      (FiniteLaw.pi (fun _ : Sym2 V=>markedPhysicalLaw p k hp hk hsum))
    1-1/(Fintype.card V:ℝ)^q₀≤μ.probability (fun z=>
      (∀ C : Fin (m+1)→V,PermutationSeparated π (3*d) C →
        (ω*tstar*sstar^m/2)*Fintype.card V≤
          ((potentialMarkedHubs (rawMarkedSpokes π d z.1 g j) C).card:ℝ)) ∧
      (∀ u : Fin 2→U,Function.Injective u →
        let T := rawMarkedPairClass π d z.1 g j u
        (kstar^(m+1)*(α*(min sstar tstar)^2/8)^(m+1)/2)*(Fintype.card V:ℝ)^(m+1)≤
          (Fintype.card {C : DenseMarkedBaseFamily P π (3*d) m (T false) (T true) //
            MarkedBaseRims P π (3*d) m z.2 C.val}:ℝ))) := by
  let θ := (min sstar tstar)^2/2
  have hθ : 0<θ := by dsimp [θ];positivity
  obtain ⟨N₁,hN₁⟩ := rawMarked_first_event m α sstar tstar ω hα hα1 hsstar htstar hω d (q₀+1) hd
  obtain ⟨N₂,hN₂⟩ := markedBase_uniform_event m (3*d) (by omega) hm α θ kstar hα
    (by linarith only [hα1]) hθ hkstar 2 (q₀+1)
  refine ⟨max 2 (max N₁ N₂),?_⟩
  intro V U Γ Color _ _ _ _ _ _ hnN hmlo hmhi P hP π hnoshort p k hp hk hsum hpmin hkmin q hq hQ s hs hS g j s₀ t₀ hg hj hslo htlo
  let n := Fintype.card V
  have hn : 0<n := by dsimp [n];omega
  let μ := FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)
  let ν := FiniteLaw.pi (fun _ : Sym2 V=>markedPhysicalLaw p k hp hk hsum)
  let J := {u : Fin 2→U // Function.Injective u}
  have hJ : Fintype.card J≤n^2 := by
    have hh := Fintype.card_subtype_le (Function.Injective (α:=Fin 2) (β:=U))
    simp only [Fintype.card_fun,Fintype.card_fin] at hh
    exact hh.trans (Nat.pow_le_pow_left hmhi 2)
  let E := fun σ : RawIntervalFamilyOutcome V U Γ Color=>
    (∀ C : Fin (m+1)→V,PermutationSeparated π (3*d) C →
      (ω*tstar*sstar^m/2)*Fintype.card V≤
        ((potentialMarkedHubs (rawMarkedSpokes π d σ g j) C).card:ℝ)) ∧
    (∀ u : Fin 2→U,Function.Injective u →
      let T := rawMarkedPairClass π d σ g j u
      Disjoint (T false) (T true) ∧ Disjoint (T false) ((T true).image π) ∧
      ∀ b : Bool,(θ*Fintype.card V≤((T b).card:ℝ)) ∧
        (∀ x : V,(1/2+α/2)*(T b).card≤((P.neighborFinset x∩T b).card:ℝ)) ∧
        (∀ x : V,(1/2+α/2)*(T b).card≤((P.neighborFinset x∩(T b).image π).card:ℝ)))
  let A := fun (σ : RawIntervalFamilyOutcome V U Γ Color) (τ : Sym2 V→Option (Bool×Bool))=>
    ∀ a : J,
      (kstar^(m+1)*(α*θ/4)^(m+1)/2)*(n:ℝ)^(m+1)≤
        (Fintype.card {C : DenseMarkedBaseFamily P π (3*d) m
          (rawMarkedPairClass π d σ g j a.val false) (rawMarkedPairClass π d σ g j a.val true) //
            MarkedBaseRims P π (3*d) m τ C.val}:ℝ)
  have hfirst : 1-1/(n:ℝ)^(q₀+1)≤μ.probability E :=
    hN₁ V U Γ Color (by omega) hmlo hmhi P hP π q hq hQ s hs hS g j s₀ t₀ hg hj hslo htlo hnoshort
  have hsecond (σ : RawIntervalFamilyOutcome V U Γ Color) (hσ : E σ) :
      1-1/(n:ℝ)^(q₀+1)≤ν.probability (A σ) := by
    apply hN₂ V J (by omega) hJ P π
      (fun a=>rawMarkedPairClass π d σ g j a.val false)
      (fun a=>rawMarkedPairClass π d σ g j a.val true)
    · intro a;exact (hσ.2 a.val a.property).2.2 false |>.1
    · intro a;exact (hσ.2 a.val a.property).2.2 true |>.1
    · intro a;exact (hσ.2 a.val a.property).2.2 false |>.2.1
    · intro a;exact (hσ.2 a.val a.property).2.2 true |>.2.1
    · exact hpmin
    · exact hkmin
  have hjoint := finiteLaw_product_good_lower μ ν E A (1/(n:ℝ)^(q₀+1))
    (1/(n:ℝ)^(q₀+1)) (by positivity) hfirst hsecond
  have hsumerr := scaled_inverse_power_le n q₀ hn 2 (by exact_mod_cast (show 2≤n by dsimp [n];omega))
  have hbound : 1-1/(n:ℝ)^q₀≤1-1/(n:ℝ)^(q₀+1)-1/(n:ℝ)^(q₀+1) := by
    convert sub_le_sub_left hsumerr 1 using 1 <;> ring
  apply (hbound.trans hjoint).trans
  apply finiteLaw_probability_mono
  intro z hz
  refine ⟨hz.1.1,?_⟩
  intro u hu
  have hh := hz.2 ⟨u,hu⟩
  have he : α*θ/4=α*(min sstar tstar)^2/8 := by dsimp [θ];ring
  simpa only [he] using hh

end Oberwolfach
