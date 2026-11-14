module

public import Oberwolfach.MarkedReferenceGlobalBalanceFromDensity
public import Oberwolfach.LongAssignedSamplingRecipe

@[expose] public section
/-! Apply the global balance bridge with the unchanged long-factor sampling
probabilities and the original host density identity. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_long_assigned_reference_global_balance
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d h r K:ℕ) (hh:1≤h)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (θ D ρ ε δ γ errR errI η:ℝ)
    (σ:RawMarkedOutcome (Fin n) U Bool Bool) (H:Bool→Fin n→U→Prop)
    (hsize:ρ*D=2*Fintype.card U)
    (hstats:MarkedReferenceStatistics P π d false false D ε δ γ
      (ρ*(1/100)/2) (ρ*((1/100)/(((r+4):ℕ):ℝ))/2)
      (1/100) ((1/100)/(((r+4):ℕ):ℝ)) σ)
    (hrows:MarkedRowsWithSpokes P π d h Finset.univ (ρ*(1/100)/2)
      (ρ*((1/100)/(((r+4):ℕ):ℝ))/2) (longAssignedIntervalProbability F hF K (r+4) θ)
      (longAssignedSpokeProbability F hF K (r+4) θ) false false errR σ H)
    (hindices:MarkedIndicesWithSpokes π d h Finset.univ (longAssignedIntervalProbability F hF K (r+4) θ)
      (longAssignedSpokeProbability F hF K (r+4) θ) false false errI σ H)
    (hbudget:2*(ε*n)+2*errI≤η*n) (hmarked:ε*n+errI≤η*n)
    (hcolumn:((((r+4):ℕ):ℝ)+1)*errR≤η*n):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2;
    (∀v,|occurrenceDegree (Sum.elim tail ktail) v-
      (∑u,if H false v u then (1:ℝ) else 0)-(∑u,if H true v u then (1:ℝ) else 0)|≤η*Fintype.card (Fin n)) ∧
    (∀v,|occurrenceDegree (Sum.elim head khead) v-
      (∑u,if H false v u then (1:ℝ) else 0)-(∑u,if H true v u then (1:ℝ) else 0)|≤η*Fintype.card (Fin n)) ∧
    (∀v,|occurrenceDegree khead v-(∑u,if H true v u then (1:ℝ) else 0)|≤η*Fintype.card (Fin n)) ∧
    (∀u,|(∑v,if H false v u then (1:ℝ) else 0)-(((r+4):ℕ):ℝ)*(∑v,if H true v u then (1:ℝ) else 0)|≤η*Fintype.card (Fin n)) :=by
  have hc:((((r+4):ℕ):ℝ))*((1/100)/(((r+4):ℕ):ℝ))=(1/100:ℝ):=by
    have hm:((((r+4):ℕ):ℝ))≠0:=by positivity
    field_simp
  have hq:∀u,longAssignedIntervalProbability F hF K (r+4) θ u false=(1/100)/(((r+4):ℕ):ℝ):=by
    intro u; rfl
  have hs:∀u,longAssignedSpokeProbability F hF K (r+4) θ u false=(((r+4):ℕ):ℝ)*((1/100)/(((r+4):ℕ):ℝ)):=by
    intro u; change (1/100:ℝ)=_; exact hc.symm
  have ht:=marked_reference_neighbourhood_balance_from_density P π d h (r+4) hh false false D ρ ε δ γ
    ((1/100)/(((r+4):ℕ):ℝ)) errR errI η (longAssignedIntervalProbability F hF K (r+4) θ)
    (longAssignedSpokeProbability F hF K (r+4) θ) σ H hq hs hsize
    (by simpa only [hc] using hstats) (by simpa only [hc] using hrows) hindices
    (by simpa only [Fintype.card_fin] using hbudget)
    (by simpa only [Fintype.card_fin] using hmarked)
    (by simpa only [Fintype.card_fin] using hcolumn)
  simpa only [Fintype.card_fin] using ht
end Oberwolfach
