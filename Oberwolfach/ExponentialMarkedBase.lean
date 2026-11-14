module

public import Oberwolfach.MarkedBaseRealization
public import Oberwolfach.MarkedBaseDensity
public import Oberwolfach.ExponentialConfigurationMargins

@[expose] public section

/-! One second-exposure event controls all supplied spoke-intersection
classes. Its order threshold is uniform over the classes and the actual
physical probabilities. The candidate count is proved from their ambient
neighbourhood bounds, not assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem markedBase_exponential_event
    (m b : ℕ) (hb : 1≤b) (hm : 2≤m) (α θ pstar : ℝ)
    (hα : 0<α) (hα1 : α≤1) (hθ : 0<θ) (hpstar : 0<pstar) (K : ℕ) :
    ∃ N : ℕ,∀ (V J : Type) [Fintype V] [LinearOrder V] [Fintype J],
      N≤Fintype.card V → Fintype.card J≤(Fintype.card V)^K →
    ∀ (P : SimpleGraph V) (π : Equiv.Perm V) (T₀ TK : J→Finset V),
      (∀ a,θ*Fintype.card V≤((T₀ a).card:ℝ)) →
      (∀ a,θ*Fintype.card V≤((TK a).card:ℝ)) →
      (∀ a x,(1/2+α/2)*(T₀ a).card≤((P.neighborFinset x∩T₀ a).card:ℝ)) →
      (∀ a x,(1/2+α/2)*(TK a).card≤((P.neighborFinset x∩TK a).card:ℝ)) →
    ∀ (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1),pstar≤p → pstar≤k →
    1-2*(Fintype.card V:ℝ)^K*Real.exp (-(2*(pstar^(m+1)*(α*θ/4)^(m+1)/2)^2/(2*((m:ℝ)+1)^2))*Fintype.card V)≤
      (FiniteLaw.pi (fun _ : Sym2 V=>markedPhysicalLaw p k hp hk hsum)).probability
        (fun σ=>∀ a : J,
          (pstar^(m+1)*(α*θ/4)^(m+1)/2)*(Fintype.card V:ℝ)^(m+1)≤
            (Fintype.card {C : DenseMarkedBaseFamily P π b m (T₀ a) (TK a) //
              MarkedBaseRims P π b m σ C.val}:ℝ)) := by
  let c := (α*θ/4)^(m+1)
  let β := pstar^(m+1)*c/2
  have hc : 0<c := by dsimp [c];positivity
  have hβ : 0<β := by dsimp [β];positivity
  obtain ⟨N₁,hN₁⟩ := denseMarkedBase_uniform_density m b (by omega) α θ hα hα1 hθ
  refine ⟨max 1 N₁,?_⟩
  intro V J _ _ _ hnN hJ P π T₀ TK hs₀ hsK hd₀ hdK p k hp hk hsum hpmin hkmin
  let n := Fintype.card V
  have hn : 0<n := by dsimp [n];omega
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  let μ := FiniteLaw.pi (fun _ : Sym2 V=>markedPhysicalLaw p k hp hk hsum)
  let failure := 2*Real.exp (-2*β^2/(2*((m:ℝ)+1)^2/n))
  have hmany (a : J) : c*(n:ℝ)^(m+1)≤Fintype.card (DenseMarkedBaseFamily P π b m (T₀ a) (TK a)) :=
    hN₁ V (by omega) P π (T₀ a) (TK a) (hs₀ a) (hsK a) (hd₀ a) (hdK a)
  have htail (a : J) : μ.probability (fun σ=>markedBaseSurvivalSum P π b m (T₀ a) (TK a) σ≤β)≤failure := by
    have hh := markedBaseSurvivalSum_lower_tail P π b m (T₀ a) (TK a) hn hb hm p k pstar c β hp hk hsum
      hpstar.le (by linarith only [hpmin,hsum,hk]) hpmin hkmin hβ (hmany a)
    have he : pstar^(m+1)*c-β=β := by dsimp [β];ring
    simpa only [he] using hh
  have hprob := finiteLaw_common_event_lower μ (Finset.univ : Finset J)
    (fun a σ=>markedBaseSurvivalSum P π b m (T₀ a) (TK a) σ≤β) (fun _=>failure)
    (fun a _=>htail a)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.mem_univ,forall_const,not_le] at hprob
  have hfail : (Fintype.card J:ℝ)*failure≤2*(n:ℝ)^K*Real.exp (-(2*β^2/(2*((m:ℝ)+1)^2))*n) := by
    simpa only [mul_one,show (2:ℝ)*2=4 by norm_num] using constant_deviation_failure_exponential 1 (2*((m:ℝ)+1)^2) β (by positivity) hβ K n hn
      (Fintype.card J:ℝ) (Nat.cast_nonneg _) (by simpa only [one_mul,Nat.cast_pow] using (show (Fintype.card J:ℝ)≤((Fintype.card V)^K:ℕ) by exact_mod_cast hJ))
  apply ((sub_le_sub_left hfail 1).trans hprob).trans
  apply finiteLaw_probability_mono
  intro σ hσ a
  have hh := (hσ a).le
  rw [markedBaseSurvivalSum_count P π b m (T₀ a) (TK a) hb hm] at hh
  exact (le_div_iff₀ (pow_pos hn0 _)).mp hh

end Oberwolfach
