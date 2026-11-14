module

public import Oberwolfach.MarkedPathRealization
public import Oberwolfach.ConfigurationFailureMargins

@[expose] public section

/-! Simultaneous physical survival for common paths with fixed external
roots. Candidate counts are derived from the class hypotheses. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem markedPath_uniform_event
    (r b : ℕ) (hb : 1≤b) (hr : 1≤r) (α θ pstar : ℝ)
    (hα : 0<α) (hα1 : α≤1) (hθ : 0<θ) (hpstar : 0<pstar) (K q₀ : ℕ) :
    ∃ N : ℕ,∀ (V J : Type) [Fintype V] [LinearOrder V] [Fintype J],
      N≤Fintype.card V → Fintype.card J≤2*(Fintype.card V)^K →
    ∀ (P : SimpleGraph V) (π : Equiv.Perm V) (T₀ TK : J→Finset V)
      (j : J→Bool) (v v' : J→V),(∀ a,v a≠v' a) →
      (∀ a,θ*Fintype.card V≤((T₀ a).card:ℝ)) →
      (∀ a,θ*Fintype.card V≤((TK a).card:ℝ)) →
      (∀ a x,(1/2+α/2)*(T₀ a).card≤((P.neighborFinset x∩T₀ a).card:ℝ)) →
      (∀ a x,(1/2+α/2)*(TK a).card≤((P.neighborFinset x∩(TK a).image π).card:ℝ)) →
    ∀ (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1),pstar≤p → pstar≤k →
    1-1/(Fintype.card V:ℝ)^q₀≤
      (FiniteLaw.pi (fun _ : Sym2 V=>markedPhysicalLaw p k hp hk hsum)).probability
        (fun σ=>∀ a : J,
          (pstar^(r+7)*(α*θ/4)^(r+4)/2)*(Fintype.card V:ℝ)^(r+4)≤
            (Fintype.card {C : DenseRootMarkedPathFamily P π b (r+3) (j a) (T₀ a) (TK a) (v a) (v' a) //
              MarkedPathRims P π b (r+3) (j a) (v a) (v' a) σ C.val}:ℝ)) := by
  let c := (α*θ/4)^(r+4)
  let β := pstar^(r+7)*c/2
  have hc : 0<c := by dsimp [c];positivity
  have hβ : 0<β := by dsimp [β];positivity
  obtain ⟨N₁,hN₁⟩ := denseRootMarkedPath_uniform_density r b hr α θ hα hα1 hθ
  obtain ⟨N₂,hN₂⟩ := constant_deviation_failure_eventually_small 2 (2*((r:ℝ)+4)*((r:ℝ)+7))
    β (by positivity) hβ K q₀
  refine ⟨max 1 (max N₁ N₂),?_⟩
  intro V J _ _ _ hnN hJ P π T₀ TK j v v' hvv hs₀ hsK hd₀ hdK p k hp hk hsum hpmin hkmin
  let n := Fintype.card V
  have hn : 0<n := by dsimp [n];omega
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  let μ := FiniteLaw.pi (fun _ : Sym2 V=>markedPhysicalLaw p k hp hk hsum)
  let failure := 2*Real.exp (-2*β^2/(2*((r:ℝ)+4)*((r:ℝ)+7)/n))
  have hmany (a : J) : c*(n:ℝ)^(r+4)≤
      Fintype.card (DenseRootMarkedPathFamily P π b (r+3) (j a) (T₀ a) (TK a) (v a) (v' a)) :=
    hN₁ V (by omega) P π (T₀ a) (TK a) (hs₀ a) (hsK a) (hd₀ a) (hdK a) (j a) (v a) (v' a)
  have htail (a : J) : μ.probability
      (fun σ=>markedPathSurvivalSum P π b (r+3) (j a) (T₀ a) (TK a) (v a) (v' a) σ≤β)≤failure := by
    have hh := markedPathSurvivalSum_lower_tail P π b (r+3) (j a) (T₀ a) (TK a) (v a) (v' a)
      hn hb (by omega) (hvv a) p k pstar c β hp hk hsum hpstar.le
      (by linarith only [hpmin,hsum,hk]) hpmin hkmin hβ (hmany a)
    have he : pstar^(r+7)*c-β=β := by dsimp [β];ring
    have hex : 2*((r:ℝ)+3+1)*((r:ℝ)+3+4)=2*((r:ℝ)+4)*((r:ℝ)+7) := by ring
    simpa only [Nat.cast_add,Nat.cast_ofNat,Nat.add_assoc,Nat.reduceAdd,he,hex] using hh
  have hprob := finiteLaw_common_event_lower μ (Finset.univ : Finset J)
    (fun a σ=>markedPathSurvivalSum P π b (r+3) (j a) (T₀ a) (TK a) (v a) (v' a) σ≤β)
    (fun _=>failure) (fun a _=>htail a)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.mem_univ,forall_const,not_le] at hprob
  have hfail : (Fintype.card J:ℝ)*failure≤1/(n:ℝ)^q₀ :=
    hN₂ n (by dsimp [n];omega) (Fintype.card J:ℝ) (Nat.cast_nonneg _) (by exact_mod_cast hJ)
  apply ((sub_le_sub_left hfail 1).trans hprob).trans
  apply finiteLaw_probability_mono
  intro σ hσ a
  have hh := (hσ a).le
  rw [markedPathSurvivalSum_count P π b (r+3) (j a) (T₀ a) (TK a) (v a) (v' a) hb (by omega) (hvv a)] at hh
  exact (le_div_iff₀ (pow_pos hn0 _)).mp hh

end Oberwolfach
