module

public import Oberwolfach.RetainedIncidenceTails
public import Oberwolfach.ConfigurationFailureMargins

@[expose] public section

/-! Lower bounds for fixed candidate sets requiring at most k physical
coins. Coordinates shared by candidates are charged by their actual
incidence bound. The one event covers every request in the fixed family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V E:Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

def retainedPatternSet (A:Finset V) (S:V→Finset E) (σ:E→Bool):Finset V:=
  A.filter (fun v=>∀ e∈S v,σ e=true)

theorem retainedPatternSet_mean_lower (A:Finset V) (S:V→Finset E)
    (k:ℕ) (hS:∀ v∈A,(S v).card≤k) (p:ℝ) (hp:0≤p) (hp1:p≤1):
    p^k*A.card≤(FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp hp1)).expectation
      (fun σ=>((retainedPatternSet A S σ).card:ℝ)):=by
  have he (v:V):(FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp hp1)).probability
      (fun σ=>∀ e∈S v,σ e=true)=p^(S v).card:=by
    rw [finiteLaw_probability_eq_expectation]
    have hf:(fun σ:E→Bool=>if ∀ e∈S v,σ e=true then (1:ℝ) else 0)=
        patternValue (S v) (fun _=>true):=by
      funext σ;rw [patternValue_indicator];split_ifs <;> rfl
    rw [hf,finiteLaw_expectation_pattern]
    simp [FiniteLaw.retentionCoin]
  change p^k*A.card≤(FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp hp1)).expectation
    (fun σ=>((A.filter (fun v=>∀ e∈S v,σ e=true)).card:ℝ))
  have hc:=finiteLaw_expectation_count (FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp hp1)) A (fun v σ=>∀ e∈S v,σ e=true)
  have hlow:p^k*A.card≤∑ v∈A,(FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp hp1)).probability (fun σ=>∀ e∈S v,σ e=true):=by
    calc
      _=∑ v∈A,p^k:=by simp;ring
      _≤_:=Finset.sum_le_sum (fun v hv=>by rw [he];exact pow_le_pow_of_le_one hp hp1 (hS v hv))
  convert hlow.trans_eq hc.symm using 1 <;> congr!

theorem retainedPatternSet_lower_tail (A:Finset V) (S:V→Finset E)
    (k:ℕ) (hS:∀ v∈A,(S v).card≤k) (p:ℝ) (hp:0≤p) (hp1:p≤1)
    (B n:ℝ) (hB:0<B) (hn:0<n) (hsize:(Fintype.card V:ℝ)≤n)
    (hread:∀ v,((S v).card:ℝ)≤B)
    (haffect:∀ e,((Finset.univ.filter (fun v=>e∈S v)).card:ℝ)≤B)
    (t:ℝ) (ht:0<t):
    (FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp hp1)).probability
      (fun σ=>((retainedPatternSet A S σ).card:ℝ)≤p^k*A.card-t)≤
      2*Real.exp (-2*t^2/(B^2*n)):=by
  let P:=fun σ:E→Bool=>fun v:V=>v∈A∧∀ e∈S v,σ e=true
  have he (σ:E→Bool):Finset.univ.filter (P σ)=retainedPatternSet A S σ:=by
    ext v;simp [P,retainedPatternSet]
  have hh:=finiteLaw_local_filter_tail (fun _:E=>FiniteLaw.retentionCoin p hp hp1) P S
    (by
      intro v σ τ hagree
      dsimp [P]
      apply and_congr_right
      intro _
      constructor
      · intro h e he;exact (hagree e he).symm.trans (h e he)
      · intro h e he;exact (hagree e he).trans (h e he))
    B n hB hn hsize hread haffect t ht
  have hh' : (FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp hp1)).probability
      (fun σ=>t≤|((retainedPatternSet A S σ).card:ℝ)-
        (FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp hp1)).expectation
          (fun τ=>((retainedPatternSet A S τ).card:ℝ))|)≤2*Real.exp (-2*t^2/(B^2*n)):=by
    convert hh using 1 <;> congr! <;> ext v <;> simp [retainedPatternSet,P]
  apply (finiteLaw_probability_mono _ _ _ ?_).trans hh'
  intro σ hσ
  have hm:=retainedPatternSet_mean_lower A S k hS p hp hp1
  have ha:=neg_le_abs (((retainedPatternSet A S σ).card:ℝ)-
    (FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp hp1)).expectation
      (fun τ=>((retainedPatternSet A S τ).card:ℝ)))
  linarith

theorem retained_pattern_lower_common_event (C B ε:ℝ) (hB:0<B) (hε:0<ε) (k K q:ℕ):
    ∃ N:ℕ,∀ n:ℕ,N≤n→∀ (V E J:Type) [Fintype V] [DecidableEq V]
      [Fintype E] [DecidableEq E] [Fintype J],Fintype.card V≤n→
      (Fintype.card J:ℝ)≤C*(n:ℝ)^K→
    ∀ (A:J→Finset V) (S:J→V→Finset E),
      (∀ j,∀ v∈A j,(S j v).card≤k)→(∀ j v,((S j v).card:ℝ)≤B)→
      (∀ j e,((Finset.univ.filter (fun v=>e∈S j v)).card:ℝ)≤B)→
    ∀ (p:ℝ) (hp:0≤p) (hp1:p≤1),
    1-1/(n:ℝ)^q≤(FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp hp1)).probability
      (fun σ=>∀ j,p^k*(A j).card-ε*n<((retainedPatternSet (A j) (S j) σ).card:ℝ)):=by
  obtain ⟨N,hN⟩:=linear_deviation_failure_eventually_small C (B^2) ε (by positivity) hε K q
  refine ⟨max 1 N,?_⟩
  intro n hn V E J _ _ _ _ _ hV hJ A S hk hread haffect p hp hp1
  have hn0:(0:ℝ)<n:=by exact_mod_cast (show 0<n by omega)
  let μ:=FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp hp1)
  let Bad:=fun (j:J) (σ:E→Bool)=>((retainedPatternSet (A j) (S j) σ).card:ℝ)≤p^k*(A j).card-ε*n
  let err:=2*Real.exp (-2*(ε*n)^2/(B^2*n))
  have hh:=finiteLaw_common_event_lower μ Finset.univ Bad (fun _=>err)
    (fun j _=>retainedPatternSet_lower_tail (A j) (S j) k (hk j) p hp hp1 B n hB hn0
      (Nat.cast_le.mpr hV) (hread j) (haffect j) (ε*n) (by positivity))
  have hsmall:=hN n (by omega) (Fintype.card J) (B^2*n) (Nat.cast_nonneg _) hJ
    (by positivity) (le_refl _)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.mem_univ,true_implies,Bad,not_le] at hh
  exact (sub_le_sub_left hsmall 1).trans hh
end Oberwolfach
