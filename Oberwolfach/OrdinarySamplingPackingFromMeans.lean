module

public import Oberwolfach.OrdinarySamplingPackingBridge
public import Oberwolfach.CycleSamplingFailureFromMeans

@[expose] public section
/-! The failure-sum hypothesis follows from quadratic vertex means and
linear pair means under the displayed fixed numerical margins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_sampling_packing_from_means
    (r B:ℕ) (hr:3≤r) (K a γ ε θ av q d:ℝ)
    (hK:0<K) (ha:0<a) (hγ:0<γ) (hγ1:γ≤1) (hε:0≤ε)
    (hmargin:a*r≤1-ε) (hθ:0<θ) (hθ1:θ≤1) (hav:0<av) (hq:0≤q)
    (hd:0<d) (hscale:2*Real.exp 1*q≤d):
    ∃ N:ℕ,∀ (V:Type) [Fintype V] [DecidableEq V] (G:SimpleGraph V)
      [DecidableEq (OrdinaryCycle G r)],N≤Fintype.card V→
    ∀ D:ℕ,Fintype.card V≤D→D≤(Fintype.card V)^B→
    ∀ (w:OrdinaryCycle G r→ℝ),
    (∀ e:G.edgeSet,∑ C,w C*ordinaryCycleIncidence G r C e=1)→
    ∀ (Bweight scale:ℝ) (hB:0≤Bweight) (hscale0:0≤scale)
      (hwb:∀ C,w C≤Bweight/(Fintype.card V:ℝ)^(r-2))
      (hp:∀ C,0≤scale*w C) (hp1:∀ C,scale*w C≤1),
    (∀ v,av*(Fintype.card V:ℝ)^2≤scale*(G.degree v:ℝ)/2)→
    (∀ v,(1-ε)*D≤(1-θ)*(scale*(G.degree v:ℝ)/2) ∧
      (1+θ)*(scale*(G.degree v:ℝ)/2)≤D)→
    scale*((r:ℝ)^2*Bweight)≤q*Fintype.card V→
    d*Fintype.card V≤K*D/Fintype.card V→
    ∃ σ:OrdinaryCycle G r→Bool,
      0<(FiniteLaw.pi (fun C=>FiniteLaw.retentionCoin (scale*w C) (hp C) (hp1 C))).mass σ ∧
      ∃ M:Finset (RetainedOrdinaryCycle G r σ),
        (∀ C∈M,∀ C'∈M,C≠C'→Disjoint (retainedOrdinaryCycleVertices C) (retainedOrdinaryCycleVertices C')) ∧
        (1-γ)*(1-ε)*Fintype.card V≤(r:ℝ)*M.card := by
  obtain ⟨Npack,hpack⟩:=ordinary_sampling_packing_bridge r B hr K a γ ε hK ha hγ hγ1 hε hmargin
  obtain ⟨Nfail,hfail⟩:=cycle_sampling_failure_from_means θ av q d hθ hav hq hd hscale
  refine ⟨max 1 (max Npack Nfail),?_⟩
  intro V _ _ G _ hn D hnD hDB w hw Bweight scale hB hscale0 hwb hp hp1 hlo hrows hpairScale ht
  have hcard:0<Fintype.card V:=by omega
  let p:=fun C:OrdinaryCycle G r=>scale*w C
  let mV:=fun v:V=>∑ C,@ite ℝ (v∈C.val.val.support) (Classical.propDecidable _) (p C) 0
  let mP:=fun z:V×V=>∑ C,@ite ℝ (z.1∈C.val.val.support ∧ z.2∈C.val.val.support) (Classical.propDecidable _) (p C) 0
  let S:=Finset.univ.filter (fun z:V×V=>z.1≠z.2 ∧ 0<mP z)
  have hV (v:V):mV v=scale*(G.degree v:ℝ)/2:=by
    have hh:=ordinary_cycle_sample_vertex_mean G r w hw scale hp hp1 v
    rw [independent_cycle_count_expectation] at hh
    exact hh
  have hP (u v:V) (huv:u≠v):mP (u,v)≤q*Fintype.card V:=by
    have hh:=ordinary_cycle_sample_pair_mean_bound G r u v huv hcard Bweight scale hB hscale0 w hwb hp hp1
    rw [independent_cycle_count_expectation] at hh
    exact hh.trans hpairScale
  have hsmall:(∑ v,2*Real.exp (-θ^2*mV v/3))+
      (∑ z∈S,(Real.exp 1*mP z/(d*Fintype.card V))^(d*Fintype.card V))<1:=by
    apply hfail V ((le_max_right Npack Nfail).trans ((le_max_right 1 _).trans hn)) S mV mP
    · intro v;rw [hV];exact hlo v
    · intro ⟨u,v⟩ hz
      have hz':=Finset.mem_filter.mp hz
      exact ⟨hz'.2.2,hP u v hz'.2.1⟩
  have he:1≤Real.exp 1:=by exact Real.one_le_exp (by norm_num)
  have hdq:q≤d:=by
    have hh:=mul_nonneg hq (show 0≤2*Real.exp 1-1 by linarith)
    nlinarith only [hh,hscale]
  have hpairbound:scale*((r:ℝ)^2*Bweight)≤d*Fintype.card V:=
    hpairScale.trans (mul_le_mul_of_nonneg_right hdq (Nat.cast_nonneg _))
  exact hpack (Fintype.card V) D ((le_max_left Npack Nfail).trans ((le_max_right 1 _).trans hn))
    hnD hDB V G (le_refl _) (hnD.trans hDB)
    w hw Bweight scale θ (d*Fintype.card V) hB hscale0 hwb hθ.le hθ1 hp hp1
    hrows hpairbound ht hsmall
end Oberwolfach
