module

public import Oberwolfach.MarkedPathRealization
public import Oberwolfach.MarkedLocalCandidateCounts
public import Oberwolfach.LocalScaleSurvivalMargins

@[expose] public section

/-! The actual path-survival event at a fixed inner scale. The leading
coefficient does not depend on the ratio of ambient to inner order. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem markedPath_local_exponential_event
    (r b : ℕ) (hb : 1≤b) (hr : 1≤r) (α θ pstar K : ℝ)
    (hα : 0<α) (hα1 : α≤1) (hθ : 0<θ) (hpstar : 0<pstar) (hK : 0<K) :
    ∃ N : ℕ,∀ (V J : Type) [Fintype V] [LinearOrder V] [Fintype J],
    ∀ a : ℕ,N≤a → a≤Fintype.card V → (Fintype.card V:ℝ)≤K*a →
    ∀ (P : SimpleGraph V) (π : Equiv.Perm V) (T₀ TK : J→Finset V)
      (j : J→Bool) (v v' : J→V), (∀ z,v z≠v' z) →
      (∀ z,θ*a≤((T₀ z).card:ℝ)) → (∀ z,θ*a≤((TK z).card:ℝ)) →
      (∀ z x,(1/2+α/2)*(T₀ z).card≤((P.neighborFinset x∩T₀ z).card:ℝ)) →
      (∀ z x,(1/2+α/2)*(TK z).card≤((P.neighborFinset x∩(TK z).image π).card:ℝ)) →
    ∀ (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1),pstar≤p → pstar≤k →
    let β := pstar^(r+7)*(α*θ/4)^(r+4)/2
    1-Fintype.card J*(2*Real.exp (-(2*(β/K^(r+4))^2/(2*((r:ℝ)+4)*((r:ℝ)+7)))*a))≤
      (FiniteLaw.pi (fun _ : Sym2 V=>markedPhysicalLaw p k hp hk hsum)).probability
        (fun σ=>∀ z : J,β*(a:ℝ)^(r+4)≤
            (Fintype.card {C : DenseRootMarkedPathFamily P π b (r+3) (j z) (T₀ z) (TK z) (v z) (v' z) //
              MarkedPathRims P π b (r+3) (j z) (v z) (v' z) σ C.val}:ℝ)) := by
  obtain ⟨N₁,hN₁⟩ := denseRootMarkedPath_local_density r b hr α θ hα hα1 hθ
  refine ⟨max 1 N₁,?_⟩
  intro V J _ _ _ a haN han hnK P π T₀ TK j v v' hvv hs₀ hsK hd₀ hdK p k hp hk hsum hpmin hkmin
  let n := Fintype.card V
  have ha : 0<a := by omega
  have hn : 0<n := ha.trans_le han
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have ha0 : (0:ℝ)<a := by exact_mod_cast ha
  let c := (α*θ/4)^(r+4)*((a:ℝ)/n)^(r+4)
  let β := pstar^(r+7)*(α*θ/4)^(r+4)/2
  let t := β*((a:ℝ)/n)^(r+4)
  have hβ : 0<β := by dsimp [β];positivity
  have ht : 0<t := by dsimp [t];positivity
  let μ := FiniteLaw.pi (fun _ : Sym2 V=>markedPhysicalLaw p k hp hk hsum)
  let failure := 2*Real.exp (-2*t^2/(2*((r:ℝ)+4)*((r:ℝ)+7)/n))
  have hscale : c*(n:ℝ)^(r+4)=(α*θ/4)^(r+4)*(a:ℝ)^(r+4) := by
    dsimp [c]
    simp only [div_pow]
    field_simp
  have hmany (z : J) : c*(n:ℝ)^(r+4)≤Fintype.card (DenseRootMarkedPathFamily P π b (r+3) (j z) (T₀ z) (TK z) (v z) (v' z)) := by
    rw [hscale]
    exact hN₁ V a (by omega) P π (T₀ z) (TK z) (hs₀ z) (hsK z) (hd₀ z) (hdK z) (j z) (v z) (v' z)
  have htail (z : J) : μ.probability (fun σ=>markedPathSurvivalSum P π b (r+3) (j z) (T₀ z) (TK z) (v z) (v' z) σ≤t)≤failure := by
    have hh := markedPathSurvivalSum_lower_tail P π b (r+3) (j z) (T₀ z) (TK z) (v z) (v' z) hn hb (by omega) (hvv z) p k pstar c t hp hk hsum
      hpstar.le (by linarith only [hpmin,hsum,hk]) hpmin hkmin ht (hmany z)
    have he : pstar^(r+7)*c-t=t := by dsimp [c,t,β];ring
    have hex : 2*((r:ℝ)+3+1)*((r:ℝ)+3+4)=2*((r:ℝ)+4)*((r:ℝ)+7) := by ring
    simpa only [Nat.cast_add,Nat.cast_ofNat,Nat.add_assoc,Nat.reduceAdd,he,hex] using hh
  have hprob := finiteLaw_common_event_lower μ (Finset.univ : Finset J)
    (fun z σ=>markedPathSurvivalSum P π b (r+3) (j z) (T₀ z) (TK z) (v z) (v' z) σ≤t) (fun _=>failure)
    (fun z _=>htail z)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.mem_univ,forall_const,not_le] at hprob
  have hfail := mul_le_mul_of_nonneg_left
    (localScale_exponential_tail a n ha han K β (2*((r:ℝ)+4)*((r:ℝ)+7)) hK hβ (by positivity) hnK (r+4))
    (Nat.cast_nonneg (Fintype.card J) : (0:ℝ)≤Fintype.card J)
  apply ((sub_le_sub_left hfail 1).trans hprob).trans
  apply finiteLaw_probability_mono
  intro σ hσ z
  have hh := (hσ z).le
  rw [markedPathSurvivalSum_count P π b (r+3) (j z) (T₀ z) (TK z) (v z) (v' z) hb (by omega) (hvv z)] at hh
  have hx := (le_div_iff₀ (pow_pos hn0 _)).mp hh
  have he : t*(n:ℝ)^(r+4)=β*(a:ℝ)^(r+4) := by
    dsimp [t]
    simp only [div_pow]
    field_simp
  rwa [he] at hx

end Oberwolfach
