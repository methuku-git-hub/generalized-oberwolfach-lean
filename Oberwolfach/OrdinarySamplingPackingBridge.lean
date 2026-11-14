module

public import Oberwolfach.OrdinarySampledCyclePacking
public import Oberwolfach.OrdinaryCycleSampleExpectations
public import Oberwolfach.CycleSamplingJointExistence

@[expose] public section
/-! From one fixed independent cycle sample to an almost spanning packing,
under the displayed deterministic means, error budget and size margins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_sampling_packing_bridge
    (r B:ℕ) (hr:3≤r) (K a γ ε:ℝ) (hK:0<K) (ha:0<a)
    (hγ:0<γ) (hγ1:γ≤1) (hε:0≤ε) (hmargin:a*r≤1-ε):
    ∃ n₀:ℕ,∀ n D:ℕ,n₀≤n→n≤D→D≤n^B→
    ∀ (V:Type) [Fintype V] [DecidableEq V] (G:SimpleGraph V)
      [DecidableEq (OrdinaryCycle G r)],
    n≤Fintype.card V→Fintype.card V≤n^B→
    ∀ (w:OrdinaryCycle G r→ℝ),
    (∀ e:G.edgeSet,∑ C,w C*ordinaryCycleIncidence G r C e=1)→
    ∀ (Bweight scale θ t:ℝ) (hB:0≤Bweight) (hscale:0≤scale)
      (hwb:∀ C,w C≤Bweight/(Fintype.card V:ℝ)^(r-2)) (hθ:0≤θ) (hθ1:θ≤1)
      (hp:∀ C,0≤scale*w C) (hp1:∀ C,scale*w C≤1),
    let p:=fun C=>scale*w C
    let mA:=fun v:V=>∑ C,@ite ℝ (v∈C.val.val.support) (Classical.propDecidable _) (p C) 0
    let mB:=fun z:V×V=>∑ C,@ite ℝ (z.1∈C.val.val.support ∧ z.2∈C.val.val.support) (Classical.propDecidable _) (p C) 0
    let S:=Finset.univ.filter (fun z:V×V=>z.1≠z.2 ∧ 0<mB z)
    (∀ v,(1-ε)*D≤(1-θ)*(scale*(G.degree v:ℝ)/2) ∧
      (1+θ)*(scale*(G.degree v:ℝ)/2)≤D)→
    scale*((r:ℝ)^2*Bweight)≤t→t≤K*D/n→
    (∑ v,2*Real.exp (-θ^2*mA v/3))+
      (∑ z∈S,(Real.exp 1*mB z/t)^t)<1→
    ∃ σ:OrdinaryCycle G r→Bool,
      0<(FiniteLaw.pi (fun C=>FiniteLaw.retentionCoin (p C) (hp C) (hp1 C))).mass σ ∧
      ∃ M:Finset (RetainedOrdinaryCycle G r σ),
        (∀ C∈M,∀ C'∈M,C≠C'→Disjoint (retainedOrdinaryCycleVertices C) (retainedOrdinaryCycleVertices C')) ∧
        (1-γ)*(1-ε)*Fintype.card V≤(r:ℝ)*M.card := by
  obtain ⟨N,hN⟩:=ordinary_sampled_cycle_packing r B hr K a γ ε hK ha hγ hγ1 hε hmargin
  refine ⟨max N 1,?_⟩
  intro n D hn hnD hDB V _ _ G _ hnV hV w hw Bweight scale θ t hB hscale hwb hθ hθ1 hp hp1 p mA mB S hrows hpairbound ht hsmall
  have hnpos:0<n:=by omega
  have hcard:0<Fintype.card V:=hnpos.trans_le hnV
  have hpair (u v:V) (huv:u≠v):mB (u,v)≤t:=by
    have hh:=ordinary_cycle_sample_pair_mean_bound G r u v huv hcard Bweight scale hB hscale w hwb hp hp1
    rw [independent_cycle_count_expectation] at hh
    exact hh.trans hpairbound
  let A:=fun v:V => fun C:OrdinaryCycle G r=>v∈C.val.val.support
  let P:=fun z:V×V => fun C:OrdinaryCycle G r=>z.1∈C.val.val.support ∧ z.2∈C.val.val.support
  have hmeans:∀ z∈S,0<∑ C,@ite ℝ (P z C) (Classical.propDecidable _) (p C) 0:=by
    intro z hz; exact (Finset.mem_filter.mp hz).2.2
  have hts:∀ z∈S,(∑ C,@ite ℝ (P z C) (Classical.propDecidable _) (p C) 0)≤t:=by
    intro ⟨u,v⟩ hz
    exact hpair u v (Finset.mem_filter.mp hz).2.1
  obtain ⟨σ,hσ,hA,hP,hzero⟩:=independent_cycle_sampling_joint_exists p hp hp1 Finset.univ A
    (fun _=>θ) (by intro _ _;exact hθ) (by intro _ _;exact hθ1) S P (fun _=>t) hmeans hts (by simpa using hsmall)
  have hmeansA (v:V):mA v=scale*(G.degree v:ℝ)/2:=by
    have hh:=ordinary_cycle_sample_vertex_mean G r w hw scale hp hp1 v
    rw [independent_cycle_count_expectation] at hh
    exact hh
  have hrows' (v:V):(1-ε)*D≤(1-θ)*mA v ∧ (1+θ)*mA v≤D:=by
    rw [hmeansA v];exact hrows v
  have hdeg:∀v,(1-ε)*D≤ independentCycleCount (A v) σ ∧ independentCycleCount (A v) σ≤D:=by
    intro v
    have h:=hA v (Finset.mem_univ v)
    have h1:independentCycleCount (A v) σ < (1+θ)*mA v:=by
      have hh:independentCycleCount (A v) σ-mA v<θ*mA v:=(abs_lt.mp h).2
      linarith only [hh]
    have h2:(1-θ)*mA v< independentCycleCount (A v) σ:=by
      have hh:-(θ*mA v)< independentCycleCount (A v) σ-mA v:=(abs_lt.mp h).1
      linarith only [hh]
    exact ⟨(hrows' v).1.trans h2.le,h1.le.trans (hrows' v).2⟩
  have hcodeg:∀u v,u≠v→independentCycleCount (P (u,v)) σ≤K*D/n:=by
    intro u v huv
    have hm:0≤mB (u,v):=by
      exact Finset.sum_nonneg (fun C _=>by split_ifs;exact hp C;exact le_rfl)
    rcases lt_or_eq_of_le hm with hpos|hzero'
    · have hz:(u,v)∈S:=Finset.mem_filter.mpr ⟨Finset.mem_univ _,huv,hpos⟩
      exact (hP (u,v) hz).le.trans ht
    · have hz:=hzero (u,v) hzero'.symm
      rw [hz]
      positivity
  obtain ⟨M,hM,hcover⟩:=hN n D ((le_max_left N 1).trans hn) hnD hDB V G σ hnV hV hdeg hcodeg
  exact ⟨σ,hσ,M,hM,hcover⟩
end Oberwolfach
