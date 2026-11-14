module

public import Oberwolfach.RawUniformRetentionRealExponents
public import Oberwolfach.RawMarkedRetention

@[expose] public section
/-! Full-row retention bounds can be added to the same retained marked sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_marked_retained_full_rows_high_probability
    (d:ℕ) (hd:2≤d) (pstar ζ δ:ℝ) (hpstar:0<pstar) (hζ:0<ζ) (hδ:0<δ):
    ∃m₀ N:ℕ,1≤m₀ ∧ ∀(V:Type) [Fintype V] [LinearOrder V] [Nonempty V],N≤Fintype.card V→
    ∀(U Γ Color:Type) [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color],
    m₀≤Fintype.card U→Fintype.card U≤Fintype.card V→
    ∀(π:Equiv.Perm V) (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (p k:ℝ) (hp:0≤p) (hk:0≤k) (hphys:2*p+2*k≤1)
    (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,(∑j,s u j) ≤ intervalUncoveredProbability d (∑g,q u g))
    (g:Γ) (t₀:ℝ) (hconst:∀u,q u g=t₀) (hmass:pstar*Fintype.card V≤t₀*Fintype.card U),
    1-δ≤(rawMarkedRetentionLaw π d hd g p k hp hk hphys q hq hQ s hs hS).probability
      (fun z=>RetainedRestrictionGood π d (fun e=>z.1 (Sum.inr e)) g
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g))
        (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ z.2):=by
  obtain ⟨m₀,N₀,hm₀,hN₀,hret⟩:=raw_uniform_retention_restrictions_real d hd 1 1 pstar ζ hpstar hζ
  obtain ⟨Nδ,hNδ⟩:=exists_nat_gt (1/δ)
  refine ⟨m₀,max (max N₀ m₀) Nδ,hm₀,?_⟩
  intro V _ _ _ hn U Γ Color _ _ _ _ hUmin hU π hnoshort p k hp hk hphys q hq hQ s hs hS g t₀ hconst hmass
  have hn0:0<Fintype.card V:=by omega
  have hnR:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn0
  have hI:(Fintype.card Unit:ℝ)≤(Fintype.card V:ℝ)^(1:ℝ):=by
    rw [Real.rpow_one]
    simp only [Fintype.card_unique,Nat.cast_one]
    exact_mod_cast hn0
  have hraw:=hret V U Γ Color Unit (by omega) hU hI π hnoshort q hq hQ s hs hS g t₀ hconst hmass
    (fun _=>Finset.univ) (fun _=>Finset.univ) (by simp) (by intro i;simpa using (show m₀≤Fintype.card V by omega))
    (by intro i;simpa using hUmin)
  have hsmall:(Fintype.card V:ℝ)^(-(1:ℝ))≤δ:=by
    rw [Real.rpow_neg_one]
    rw [←one_div]
    apply (div_le_iff₀ hnR).2
    have hh:1/δ<(Fintype.card V:ℝ):=lt_of_lt_of_le hNδ (by exact_mod_cast (show Nδ≤Fintype.card V by omega))
    have hh':1<(Fintype.card V:ℝ)*δ:=(div_lt_iff₀ hδ).1 hh
    linarith
  let Good:=fun (z:RawRetainedIntervalOutcome (U:=U) (Γ:=Γ) (Color:=Color) π d g)=>RetainedRestrictionGood π d z.1 g
    (startRetentionMinimum (rawStartHubSet π d z.1 g)) (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ z.2
  have hGood:1-δ≤(rawUniformRetentionLaw π d hd g q hq hQ s hs hS).probability Good:=by
    apply (sub_le_sub_left hsmall 1).trans
    apply hraw.trans
    apply finiteLaw_probability_mono
    intro z hz
    exact hz.2
  rw [←rawMarkedRetentionLaw_interval_projection π d hd g p k hp hk hphys q hq hQ s hs hS Good] at hGood
  exact hGood
end Oberwolfach
