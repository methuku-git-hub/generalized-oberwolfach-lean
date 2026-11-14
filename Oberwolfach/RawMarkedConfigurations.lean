module

public import Oberwolfach.RawMarkedPaths
public import Oberwolfach.SampledCommonMarkedCycles
public import Oberwolfach.SampledCommonMarkedPaths

@[expose] public section

/-! One common raw-sample event for compatible hubs, common cycles and
both root-omitted common-path types. All numerical lower coefficients are
fixed before the interval length and actual feasible marginal arrays. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem rawMarked_configurations_event
    (r : ℕ) (hr : 1≤r) (α sstar tstar kstar ω : ℝ) (hα : 0<α) (hα1 : α≤1/2)
    (hsstar : 0<sstar) (htstar : 0<tstar) (hkstar : 0<kstar) (hω : 0<ω) :
    ∃ β : ℝ,0<β ∧ ∀ d q₀ : ℕ,∀ hd : 2≤d,∃ N : ℕ,∀ (V U Γ Color : Type)
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
    1-1/(Fintype.card V:ℝ)^q₀≤μ.probability (fun z=>
      (∀ C : Fin (r+5)→V,PermutationSeparated π (3*d) C →
        32*β*Fintype.card V≤((potentialMarkedHubs (rawMarkedSpokes π d z.1 g j₀) C).card:ℝ)) ∧
      (∀ u : Fin 2→U,Function.Injective u →
        16*β*(Fintype.card V:ℝ)^(r+5)≤
          (Fintype.card (SampledCommonMarkedCycle P π d (r+4) z.1 z.2 g j₀ u):ℝ)) ∧
      (∀ v v' : V,v≠v' → ∀ u : Fin 2→U,Function.Injective u → ∀ j : Bool,
        16*β*(Fintype.card V:ℝ)^(r+4)≤
          (Fintype.card (SampledCommonMarkedPath P π d (r+3) j v v' z.1 z.2 g j₀ u):ℝ))) := by
  let a := α*(min sstar tstar)^2/8
  let H := ω*tstar*sstar^(r+4)/2
  let B := kstar^(r+5)*a^(r+5)/2
  let F := kstar^(r+7)*a^(r+4)/2
  let β := min (H/32) (min (B/16) (F/16))
  have ha : 0<a := by dsimp [a];positivity
  have hH : 0<H := by dsimp [H];positivity
  have hB : 0<B := by dsimp [B];positivity
  have hF : 0<F := by dsimp [F];positivity
  have hβ : 0<β := by dsimp [β];positivity
  have hβH : 32*β≤H := by have hh:=min_le_left (H/32) (min (B/16) (F/16));dsimp [β];linarith only [hh]
  have hβB : 16*β≤B := by
    have hh:=(min_le_right (H/32) (min (B/16) (F/16))).trans (min_le_left (B/16) (F/16))
    dsimp [β];linarith only [hh]
  have hβF : 16*β≤F := by
    have hh:=(min_le_right (H/32) (min (B/16) (F/16))).trans (min_le_right (B/16) (F/16))
    dsimp [β];linarith only [hh]
  refine ⟨β,hβ,?_⟩
  intro d q₀ hd
  obtain ⟨N₁,hN₁⟩ := rawMarked_base_cycles_event (r+4) (by omega) α sstar tstar kstar ω
    hα hα1 hsstar htstar hkstar hω d (q₀+1) hd
  obtain ⟨N₂,hN₂⟩ := rawMarked_paths_event r hr α sstar tstar kstar ω
    hα hα1 hsstar htstar hkstar hω d (q₀+1) hd
  refine ⟨max 2 (max N₁ N₂),?_⟩
  intro V U Γ Color _ _ _ _ _ _ hnN hmlo hmhi P hP π hnoshort p k hp hk hsum hpmin hkmin q hq hQ s hs hS g j₀ s₀ t₀ hg hj hslo htlo
  let n := Fintype.card V
  have hn : 0<n := by dsimp [n];omega
  let μ := (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).prod
    (FiniteLaw.pi (fun _ : Sym2 V=>markedPhysicalLaw p k hp hk hsum))
  let E := fun z : RawIntervalFamilyOutcome V U Γ Color×(Sym2 V→Option (Bool×Bool))=>
    (∀ C : Fin (r+5)→V,PermutationSeparated π (3*d) C →
      H*n≤((potentialMarkedHubs (rawMarkedSpokes π d z.1 g j₀) C).card:ℝ)) ∧
    (∀ u : Fin 2→U,Function.Injective u →
      let T := rawMarkedPairClass π d z.1 g j₀ u
      B*(n:ℝ)^(r+5)≤(Fintype.card {C : DenseMarkedBaseFamily P π (3*d) (r+4) (T false) (T true) //
        MarkedBaseRims P π (3*d) (r+4) z.2 C.val}:ℝ))
  have hbase : 1-1/(n:ℝ)^(q₀+1)≤μ.probability E :=
    hN₁ V U Γ Color (by omega) hmlo hmhi P hP π hnoshort p k hp hk hsum hpmin hkmin q hq hQ s hs hS g j₀ s₀ t₀ hg hj hslo htlo
  have hpath := hN₂ V U Γ Color (by omega) hmlo hmhi P hP π hnoshort p k hp hk hsum hpmin hkmin q hq hQ s hs hS g j₀ s₀ t₀ hg hj hslo htlo
  have hjoint := finiteLaw_good_intersection μ E _ (1/(n:ℝ)^(q₀+1)) hpath
  have hsumerr := scaled_inverse_power_le n q₀ hn 2 (by exact_mod_cast (show 2≤n by dsimp [n];omega))
  have hbound : 1-1/(n:ℝ)^q₀≤(1-1/(n:ℝ)^(q₀+1))-1/(n:ℝ)^(q₀+1) := by
    convert sub_le_sub_left hsumerr 1 using 1 <;> ring
  apply (hbound.trans ((sub_le_sub_right hbase _).trans hjoint)).trans
  apply finiteLaw_probability_mono
  intro z hz
  refine ⟨?_,?_,?_⟩
  · intro C hC
    exact (mul_le_mul_of_nonneg_right hβH (Nat.cast_nonneg _)).trans (hz.1.1 C hC)
  · intro u hu
    have hh := hz.1.2 u hu
    have hc := survivingBase_card_le_common_cycle P π d (r+4) z.1 z.2 g j₀ u
    exact ((mul_le_mul_of_nonneg_right hβB (by positivity)).trans hh).trans (by exact_mod_cast hc)
  · intro v v' hvv u hu j
    have hh := hz.2 v v' hvv u hu j
    have hc := survivingPath_card_le_common_path P π d (r+3) j v v' z.1 z.2 g j₀ u (by omega)
    exact ((mul_le_mul_of_nonneg_right hβF (by positivity)).trans hh).trans (by exact_mod_cast hc)

end Oberwolfach
