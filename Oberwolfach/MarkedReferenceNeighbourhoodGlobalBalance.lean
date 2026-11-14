module

public import Oberwolfach.MarkedGlobalBalanceFromDegrees
public import Oberwolfach.MarkedReferenceStatisticsSampleDegrees
public import Oberwolfach.MarkedNeighbourhoodSingleSpokeDegrees

@[expose] public section
/-! Reference statistics and singleton retained-spoke tests imply all four
global near-balance estimates required by marked sparse correction. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_reference_and_neighbourhood_global_balance
    (P:SimpleGraph V) (π:Equiv.Perm V) (d h m:ℕ) (hh:1≤h)
    (g:Γ) (j:Color) (D ε δ γ p k s₀ t₀ errR errI η:ℝ)
    (q:U→Γ→ℝ) (s:U→Color→ℝ) (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hq:∀u,q u g=t₀) (hs:∀u,s u j=s₀)
    (hp:p*D=s₀*Fintype.card U) (hk:k*D=t₀*Fintype.card U) (hst:s₀=(m:ℝ)*t₀)
    (hstats:MarkedReferenceStatistics P π d g j D ε δ γ p k s₀ t₀ σ)
    (hrows:MarkedRowsWithSpokes P π d h Finset.univ p k q s g j errR σ H)
    (hindices:MarkedIndicesWithSpokes π d h Finset.univ q s g j errI σ H)
    (hbudget:2*(ε*Fintype.card V)+2*errI≤η*Fintype.card V)
    (hmarked:ε*Fintype.card V+errI≤η*Fintype.card V)
    (hcolumn:((m:ℝ)+1)*errR≤η*Fintype.card V):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2;
    (∀v,|occurrenceDegree (Sum.elim tail ktail) v-
      (∑u,if H false v u then (1:ℝ) else 0)-(∑u,if H true v u then (1:ℝ) else 0)|≤η*Fintype.card V) ∧
    (∀v,|occurrenceDegree (Sum.elim head khead) v-
      (∑u,if H false v u then (1:ℝ) else 0)-(∑u,if H true v u then (1:ℝ) else 0)|≤η*Fintype.card V) ∧
    (∀v,|occurrenceDegree khead v-(∑u,if H true v u then (1:ℝ) else 0)|≤η*Fintype.card V) ∧
    (∀u,|(∑v,if H false v u then (1:ℝ) else 0)-(m:ℝ)*(∑v,if H true v u then (1:ℝ) else 0)|≤η*Fintype.card V):=by
  intro E K tail head ktail khead
  obtain ⟨hdo,hdi,hko,hki⟩:=marked_reference_statistics_sample_arc_degrees P π d g j D ε δ γ p k s₀ t₀ σ hstats
  have hden0:∀u,(if false then q u g else s u j)=s₀:=by intro u; simpa using hs u
  have hden1:∀u,(if true then q u g else s u j)=t₀:=by intro u; simpa using hq u
  obtain ⟨hcol0,hrow0⟩:=marked_neighbourhood_single_spoke_degrees P π d h hh p k q s g j errR errI s₀ σ H false hden0 hrows hindices
  obtain ⟨hcol1,hrow1⟩:=marked_neighbourhood_single_spoke_degrees P π d h hh p k q s g j errR errI t₀ σ H true hden1 hrows hindices
  have hr0:∀v,|(∑u,if H false v u then (1:ℝ) else 0)-p*D|≤errI:=by
    intro v;rw [hp];exact (hrow0 v).le
  have hr1:∀v,|(∑u,if H true v u then (1:ℝ) else 0)-k*D|≤errI:=by
    intro v;rw [hk];exact (hrow1 v).le
  have hc0:∀u,|(∑v,if H false v u then (1:ℝ) else 0)-s₀*Fintype.card V|≤errR:=fun u=>(hcol0 u).le
  have hc1:∀u,|(∑v,if H true v u then (1:ℝ) else 0)-t₀*Fintype.card V|≤errR:=fun u=>(hcol1 u).le
  have ht:s₀*Fintype.card V=(m:ℝ)*(t₀*Fintype.card V):=by rw [hst];ring
  obtain ⟨ha,hb,hc,hd⟩:=marked_global_balance_from_degree_approximations tail head ktail khead (H false) (H true) m
    (p*D) (k*D) (s₀*Fintype.card V) (t₀*Fintype.card V) (ε*Fintype.card V) errI errR ht hdo hdi hko hki hr0 hr1 hc0 hc1
  exact ⟨fun v=>(ha v).trans hbudget,fun v=>(hb v).trans hbudget,fun v=>(hc v).trans hmarked,fun u=>(hd u).trans hcolumn⟩
end Oberwolfach
