module

public import Oberwolfach.MarkedBaseRealization
public import Oberwolfach.MarkedLocalCandidateCounts
public import Oberwolfach.LocalScaleSurvivalMargins

@[expose] public section

/-! The actual cycle-survival event at a fixed inner scale. The leading
coefficient does not depend on the ratio of ambient to inner order. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem markedBase_local_exponential_event
    (m b : ℕ) (hb : 1≤b) (hm : 2≤m) (α θ pstar K : ℝ)
    (hα : 0<α) (hα1 : α≤1) (hθ : 0<θ) (hpstar : 0<pstar) (hK : 0<K) :
    ∃ N : ℕ,∀ (V J : Type) [Fintype V] [LinearOrder V] [Fintype J],
    ∀ a : ℕ,N≤a → a≤Fintype.card V → (Fintype.card V:ℝ)≤K*a →
    ∀ (P : SimpleGraph V) (π : Equiv.Perm V) (T₀ TK : J→Finset V),
      (∀ z,θ*a≤((T₀ z).card:ℝ)) → (∀ z,θ*a≤((TK z).card:ℝ)) →
      (∀ z x,(1/2+α/2)*(T₀ z).card≤((P.neighborFinset x∩T₀ z).card:ℝ)) →
      (∀ z x,(1/2+α/2)*(TK z).card≤((P.neighborFinset x∩TK z).card:ℝ)) →
    ∀ (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1),pstar≤p → pstar≤k →
    let β := pstar^(m+1)*(α*θ/4)^(m+1)/2
    1-Fintype.card J*(2*Real.exp (-(2*(β/K^(m+1))^2/(2*((m:ℝ)+1)^2))*a))≤
      (FiniteLaw.pi (fun _ : Sym2 V=>markedPhysicalLaw p k hp hk hsum)).probability
        (fun σ=>∀ z : J,β*(a:ℝ)^(m+1)≤
            (Fintype.card {C : DenseMarkedBaseFamily P π b m (T₀ z) (TK z) //
              MarkedBaseRims P π b m σ C.val}:ℝ)) := by
  obtain ⟨N₁,hN₁⟩ := denseMarkedBase_local_density m b (by omega) α θ hα hα1 hθ
  refine ⟨max 1 N₁,?_⟩
  intro V J _ _ _ a haN han hnK P π T₀ TK hs₀ hsK hd₀ hdK p k hp hk hsum hpmin hkmin
  let n := Fintype.card V
  have ha : 0<a := by omega
  have hn : 0<n := ha.trans_le han
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have ha0 : (0:ℝ)<a := by exact_mod_cast ha
  let c := (α*θ/4)^(m+1)*((a:ℝ)/n)^(m+1)
  let β := pstar^(m+1)*(α*θ/4)^(m+1)/2
  let t := β*((a:ℝ)/n)^(m+1)
  have hβ : 0<β := by dsimp [β];positivity
  have ht : 0<t := by dsimp [t];positivity
  let μ := FiniteLaw.pi (fun _ : Sym2 V=>markedPhysicalLaw p k hp hk hsum)
  let failure := 2*Real.exp (-2*t^2/(2*((m:ℝ)+1)^2/n))
  have hscale : c*(n:ℝ)^(m+1)=(α*θ/4)^(m+1)*(a:ℝ)^(m+1) := by
    dsimp [c]
    simp only [div_pow]
    field_simp
  have hmany (z : J) : c*(n:ℝ)^(m+1)≤Fintype.card (DenseMarkedBaseFamily P π b m (T₀ z) (TK z)) := by
    rw [hscale]
    exact hN₁ V a (by omega) P π (T₀ z) (TK z) (hs₀ z) (hsK z) (hd₀ z) (hdK z)
  have htail (z : J) : μ.probability (fun σ=>markedBaseSurvivalSum P π b m (T₀ z) (TK z) σ≤t)≤failure := by
    have hh := markedBaseSurvivalSum_lower_tail P π b m (T₀ z) (TK z) hn hb hm p k pstar c t hp hk hsum
      hpstar.le (by linarith only [hpmin,hsum,hk]) hpmin hkmin ht (hmany z)
    have he : pstar^(m+1)*c-t=t := by dsimp [c,t,β];ring
    simpa only [he] using hh
  have hprob := finiteLaw_common_event_lower μ (Finset.univ : Finset J)
    (fun z σ=>markedBaseSurvivalSum P π b m (T₀ z) (TK z) σ≤t) (fun _=>failure)
    (fun z _=>htail z)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.mem_univ,forall_const,not_le] at hprob
  have hfail := mul_le_mul_of_nonneg_left
    (localScale_exponential_tail a n ha han K β (2*((m:ℝ)+1)^2) hK hβ (by positivity) hnK (m+1))
    (Nat.cast_nonneg (Fintype.card J) : (0:ℝ)≤Fintype.card J)
  apply ((sub_le_sub_left hfail 1).trans hprob).trans
  apply finiteLaw_probability_mono
  intro σ hσ z
  have hh := (hσ z).le
  rw [markedBaseSurvivalSum_count P π b m (T₀ z) (TK z) hb hm] at hh
  have hx := (le_div_iff₀ (pow_pos hn0 _)).mp hh
  have he : t*(n:ℝ)^(m+1)=β*(a:ℝ)^(m+1) := by
    dsimp [t]
    simp only [div_pow]
    field_simp
  rwa [he] at hx

end Oberwolfach
