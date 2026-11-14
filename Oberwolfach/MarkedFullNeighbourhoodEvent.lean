module

public import Oberwolfach.MarkedRowCommonEvent
public import Oberwolfach.MarkedIndexCommonEvent
public import Oberwolfach.ConfigurationFailureMargins
public import Oberwolfach.GoodPlacementEvents

@[expose] public section

/-! All bounded row and separated index tests on the full host, in one
original raw event. The order threshold is uniform over the actual host
and all supplied marginal arrays. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_full_neighbourhood_common_event (h d Q:ℕ) (hd:2≤d) (ω ε:ℝ) (hω:0<ω) (hε:0<ε):
    ∃ N:ℕ,2≤N∧∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],N≤Fintype.card V→Fintype.card U≤Fintype.card V→
      ω*Fintype.card V≤(Fintype.card U:ℝ)→
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V),(∀ x l,0<l→l<2*d+1→(π^l) x≠x)→
    ∀ (p k:ℝ) (hp:0≤p) (hk:0≤k) (hphys:2*p+2*k≤1)
      (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g)) (g:Γ) (j:Color),
    1-1/(Fintype.card V:ℝ)^Q≤
      (FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hphys d hd q hq hQ s hs hS)).probability
        (fun σ=>RawMarkedRows P π d h Finset.univ p k q s g j (ε*Fintype.card V) σ∧
          RawMarkedIndices π d h Finset.univ q s g j (ε*Fintype.card U) σ):=by
  obtain ⟨Nr,hr⟩:=linear_deviation_failure_eventually_small ((5:ℝ)^(2*h)*3^h)
    ((8*(d:ℝ)+6)^2*(2*(2*(h:ℝ)+1))) ε (by positivity) hε (3*h) (Q+1)
  obtain ⟨Ni,hi⟩:=linear_deviation_failure_eventually_small ((3:ℝ)^h)
    ((8*(d:ℝ)+6)^2*((h:ℝ)+1)) (ε*ω) (by positivity) (mul_pos hε hω) h (Q+1)
  refine ⟨max 2 (max Nr Ni),le_max_left _ _,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hU hωU P π hπ p k hp hk hphys q hq hQ s hs hS g j
  have hn2:2≤Fintype.card V:=by omega
  have hn0:0<Fintype.card V:=by omega
  have hnR:(0:ℝ)<Fintype.card V:=Nat.cast_pos.mpr hn0
  have hn1:(1:ℝ)≤Fintype.card V:=by exact_mod_cast hn0
  have hUR:(Fintype.card U:ℝ)≤Fintype.card V:=by exact_mod_cast hU
  have huR:(0:ℝ)<Fintype.card U:=(mul_pos hω hnR).trans_le hωU
  have hV4:4*(Fintype.card V:ℝ)+1≤5*Fintype.card V:=by linarith only [hn1]
  have hU2:2*(Fintype.card U:ℝ)+1≤3*Fintype.card V:=by linarith only [hn1,hUR]
  have hV2:2*(Fintype.card V:ℝ)+1≤3*Fintype.card V:=by linarith only [hn1]
  have hcr:(4*(Fintype.card V:ℝ)+1)^(2*h)*(2*(Fintype.card U:ℝ)+1)^h≤
      ((5:ℝ)^(2*h)*3^h)*(Fintype.card V:ℝ)^(3*h):=by
    calc
      _≤(5*(Fintype.card V:ℝ))^(2*h)*(3*(Fintype.card V:ℝ))^h:=by gcongr
      _=_:=by rw [show 3*h=2*h+h by omega,pow_add];simp only [mul_pow];ring
  have hci:(2*(Fintype.card V:ℝ)+1)^h≤(3:ℝ)^h*(Fintype.card V:ℝ)^h:=by
    simpa only [mul_pow] using pow_le_pow_left₀ (by positivity) hV2 h
  have htr:=hr (Fintype.card V) (by omega) _ ((8*(d:ℝ)+6)^2*(2*(2*(h:ℝ)+1)*Fintype.card V))
    (by positivity) hcr (by positivity) (by ring_nf;exact le_rfl)
  have hti:=hi (Fintype.card V) (by omega) _ ((8*(d:ℝ)+6)^2*(((h:ℝ)+1)*Fintype.card U))
    (by positivity) hci (by positivity) (by simpa only [mul_assoc] using (mul_le_mul_of_nonneg_left hUR (show 0≤(8*(d:ℝ)+6)^2*((h:ℝ)+1) by positivity)))
  let μ:=FiniteLaw.pi (rawMarkedWheelLaw (V:=V) p k hp hk hphys d hd q hq hQ s hs hS)
  have hrow:1-1/(Fintype.card V:ℝ)^(Q+1)≤μ.probability
      (RawMarkedRows P π d h Finset.univ p k q s g j (ε*Fintype.card V)):=by
    have hh:=rawMarkedRows_common_event P π d hd p k hp hk hphys q hq hQ s hs hS hπ
      Finset.univ (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp hn0)) h g j (ε*Fintype.card V) (by positivity)
    simp only [Finset.card_univ] at hh
    exact (sub_le_sub_left htr 1).trans hh
  have hindex:1-1/(Fintype.card V:ℝ)^(Q+1)≤μ.probability
      (RawMarkedIndices π d h Finset.univ q s g j (ε*Fintype.card U)):=by
    have hh:=rawMarkedIndices_common_event π d hd p k hp hk hphys q hq hQ s hs hS hπ
      Finset.univ (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp (Nat.cast_pos.mp huR))) h g j
      ((ε*ω)*Fintype.card V) (by positivity)
    simp only [Finset.card_univ] at hh
    apply ((sub_le_sub_left hti 1).trans hh).trans
    apply finiteLaw_probability_mono
    intro σ hσ J hJ hsep
    exact (hσ J hJ hsep).trans_le (by nlinarith only [mul_le_mul_of_nonneg_left hωU hε.le])
  have hh:=finiteLaw_good_intersection μ (RawMarkedRows P π d h Finset.univ p k q s g j (ε*Fintype.card V)) _ (1/(Fintype.card V:ℝ)^(Q+1)) hindex
  have hnum:=scaled_inverse_power_le (Fintype.card V) Q hn0 2 (by exact_mod_cast hn2)
  have hnum' : 2*(1/(Fintype.card V:ℝ)^(Q+1))≤1/(Fintype.card V:ℝ)^Q:=by
    convert hnum using 1 <;> ring
  change 1-1/(Fintype.card V:ℝ)^Q≤μ.probability _
  linarith only [hh,hrow,hnum']

end Oberwolfach
