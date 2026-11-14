module

public import Oberwolfach.MarkedReferenceRelabelSampleDegrees
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
variable {V W U Z Γ Color:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z] [Fintype Γ] [Fintype Color]
  [Nonempty V] [Nonempty W] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem marked_relabelled_reference_neighbourhood_global_balance
    (F:W↪oV) (f:W≃V) (hf:∀w,f w=F w) (uEq:Z≃U)
    (P:SimpleGraph V) (π:Equiv.Perm V) (ρ:Equiv.Perm W) (hc:∀w,f (ρ w)=π (f w))
    (d h m:ℕ) (hh:1≤h)
    (g:Γ) (j:Color) (D ε δ γ p k s₀ t₀ errR errI η:ℝ)
    (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a) (H:Bool→V→U→Prop)
    (hq:∀u,q u g=t₀) (hs:∀u,s u j=s₀)
    (hp:p*D=s₀*Fintype.card U) (hk:k*D=t₀*Fintype.card U) (hst:s₀=(m:ℝ)*t₀)
    (hstats:MarkedReferenceStatistics (P.comap F) ρ d g j D ε δ γ p k s₀ t₀
      (markedRetainedPairRestriction f uEq π ρ hc d a z).1)
    (hrows:MarkedRowsWithSpokes P π d h Finset.univ p k q s g j errR z.1 H)
    (hindices:MarkedIndicesWithSpokes π d h Finset.univ q s g j errI z.1 H)
    (hbudget:2*(ε*Fintype.card V)+2*errI≤η*Fintype.card V)
    (hmarked:ε*Fintype.card V+errI≤η*Fintype.card V)
    (hcolumn:((m:ℝ)+1)*errR≤η*Fintype.card V):
    let E:=MarkedSampleArc P π (3*d) (fun e=>z.1 (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>z.1 (Sum.inl e)) true
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
  obtain ⟨hdo,hdi,hko,hki⟩:=marked_reference_relabel_sample_degrees F f hf uEq π ρ hc P d a g j z D ε δ γ p k s₀ t₀ hstats
  have hden0:∀u,(if false then q u g else s u j)=s₀:=by intro u; simpa using hs u
  have hden1:∀u,(if true then q u g else s u j)=t₀:=by intro u; simpa using hq u
  obtain ⟨hcol0,hrow0⟩:=marked_neighbourhood_single_spoke_degrees P π d h hh p k q s g j errR errI s₀ z.1 H false hden0 hrows hindices
  obtain ⟨hcol1,hrow1⟩:=marked_neighbourhood_single_spoke_degrees P π d h hh p k q s g j errR errI t₀ z.1 H true hden1 hrows hindices
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
