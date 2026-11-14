module

public import Oberwolfach.MarkedRetainedFullNeighbourhoodEvent
public import Oberwolfach.MarkedSampledHostCounts

@[expose] public section

/-! Actual marked extension counts on the globally retained experiment.
The minimum size is chosen before the host and its marginal arrays; the
permutation radius affects only this minimum size. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_retained_extension_event (l d Q:ℕ) (hd:2≤d) (ω γ pstar pret:ℝ)
    (hω:0<ω) (hγ:0<γ) (hγ1:γ≤1) (hpstar:0<pstar) (hpstar1:pstar≤1) (hpret:0<pret):
    ∃ N:ℕ,2≤N∧∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [Nonempty V] [DecidableEq U],N≤Fintype.card V→Fintype.card U≤Fintype.card V→
      ω*Fintype.card V≤(Fintype.card U:ℝ)→
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V),(∀ x l,0<l→l<2*d+1→(π^l) x≠x)→
      (∀ x,(1/2+γ/2)*Fintype.card V≤(P.degree x:ℝ))→
    ∀ (p k:ℝ) (hp:0≤p) (hk:0≤k) (hphys:2*p+2*k≤1),pstar≤p→pstar≤k→
    ∀ (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g)) (g:Γ) (j:Color)
      (t₀:ℝ),(∀ u,q u g=t₀)→pret*Fintype.card V≤t₀*Fintype.card U→
      (∀ u,pstar≤q u g)→(∀ u,pstar≤s u j)→
    1-1/(Fintype.card V:ℝ)^Q≤
      (rawMarkedRetentionLaw π d hd g p k hp hk hphys q hq hQ s hs hS).probability
        (fun z=>let H:Bool→V→U→Prop := retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) g (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g)) z.2 g j
          MarkedHostExtensionCounts
            (fun e:MarkedSampleArc P π (3*d) (fun e=>z.1 (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
            (fun e:MarkedSampleArc P π (3*d) (fun e=>z.1 (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
            (H false) (H true) π (3*d) l
            ((pstar^4*γ/4)*Fintype.card V) ((pstar^(l+11)*ω/2)*Fintype.card V)):=by
  let ε:=min (pstar^4*γ/4) (pstar^(l+11)/2)
  have hε:0<ε:=by dsimp[ε];positivity
  obtain ⟨M,N,hM,hN,hreal⟩:=marked_retained_full_neighbourhood_event (l+11) d Q hd ω ε pret hω hε hpret
  let N':=max N (max M (max (Nat.ceil ((M:ℝ)/ω)) (Nat.ceil (4*(2*(3*d:ℕ)+1:ℝ)/γ))))
  refine ⟨N',hN.trans (le_max_left _ _),?_⟩
  intro V U Γ Color _ _ _ _ _ _ _ hn hU hωU P π hπ hdeg p k hp hk hphys hpp hpk q hq hQ s hs hS g j t₀ ht₀ hmass hpq hps
  have hnN:N≤Fintype.card V:=by dsimp[N'] at hn;omega
  have hnM:M≤Fintype.card V:=by dsimp[N'] at hn;omega
  have hnω:(M:ℝ)/ω≤Fintype.card V:=
    (Nat.le_ceil _).trans (by exact_mod_cast (show Nat.ceil ((M:ℝ)/ω)≤Fintype.card V by dsimp[N'] at hn;omega))
  have hMU:M≤Fintype.card U:=by
    have hh: (M:ℝ)≤Fintype.card U:=((div_le_iff₀ hω).mp hnω).trans (by simpa only [mul_comm] using hωU)
    exact_mod_cast hh
  have hnc:4*(2*(3*d:ℕ)+1:ℝ)/γ≤Fintype.card V:=
    (Nat.le_ceil _).trans (by exact_mod_cast (show Nat.ceil (4*(2*(3*d:ℕ)+1:ℝ)/γ)≤Fintype.card V by dsimp[N'] at hn;omega))
  have hloss:2*(2*(3*d:ℕ)+1:ℝ)≤γ*Fintype.card V/2:=by
    have hh:=(div_le_iff₀ hγ).mp hnc
    nlinarith only [hh]
  have hb:=hreal V U Γ Color hnN hnM hMU hU hωU P π hπ p k hp hk hphys q hq hQ s hs hS g j t₀ ht₀ hmass
  apply hb.trans
  apply finiteLaw_probability_mono
  intro z hz
  exact marked_sampled_host_extension_counts P π d l p k q s g j ε γ pstar ω hpstar hpstar1 hγ hγ1
    hpp hpk hpq hps (min_le_left _ _) (min_le_right _ _) hloss hdeg hωU z.1 _ hz.1 hz.2

end Oberwolfach
