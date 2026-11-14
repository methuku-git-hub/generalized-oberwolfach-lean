module

public import Oberwolfach.MarkedRelabelledReferenceNeighbourhoodBalance
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

theorem marked_long_assigned_relabelled_reference_global_balance
    {n:ℕ} {U W Z:Type} [Fintype U] [DecidableEq U] [Fintype W] [Fintype Z]
    [Nonempty (Fin n)] [Nonempty W] [LinearOrder W] [DecidableEq Z]
    (F₀:W↪oFin n) (f:W≃Fin n) (hf:∀w,f w=F₀ w) (uEq:Z≃U)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (πW:Equiv.Perm W) (hc:∀w,f (πW w)=π (f w))
    (d h r K:ℕ) (hh:1≤h)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (θ D ρ ε δ γ errR errI η:ℝ)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Bool) π d false) (H:Bool→Fin n→U→Prop)
    (hsize:ρ*D=2*Fintype.card U)
    (hstats:MarkedReferenceStatistics (P.comap F₀) πW d false false D ε δ γ
      (ρ*(1/100)/2) (ρ*((1/100)/(((r+4):ℕ):ℝ))/2)
      (1/100) ((1/100)/(((r+4):ℕ):ℝ)) (markedRetainedPairRestriction f uEq π πW hc d false z).1)
    (hrows:MarkedRowsWithSpokes P π d h Finset.univ (ρ*(1/100)/2)
      (ρ*((1/100)/(((r+4):ℕ):ℝ))/2) (longAssignedIntervalProbability F hF K (r+4) θ)
      (longAssignedSpokeProbability F hF K (r+4) θ) false false errR z.1 H)
    (hindices:MarkedIndicesWithSpokes π d h Finset.univ (longAssignedIntervalProbability F hF K (r+4) θ)
      (longAssignedSpokeProbability F hF K (r+4) θ) false false errI z.1 H)
    (hbudget:2*(ε*n)+2*errI≤η*n) (hmarked:ε*n+errI≤η*n)
    (hcolumn:((((r+4):ℕ):ℝ)+1)*errR≤η*n):
    let E:=MarkedSampleArc P π (3*d) (fun e=>z.1 (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>z.1 (Sum.inl e)) true
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
  have hconstant:((((r+4):ℕ):ℝ))*((1/100)/(((r+4):ℕ):ℝ))=(1/100:ℝ):=by
    have hm:((((r+4):ℕ):ℝ))≠0:=by positivity
    field_simp
  have hq:∀u,longAssignedIntervalProbability F hF K (r+4) θ u false=(1/100)/(((r+4):ℕ):ℝ):=by
    intro u; rfl
  have hs:∀u,longAssignedSpokeProbability F hF K (r+4) θ u false=(((r+4):ℕ):ℝ)*((1/100)/(((r+4):ℕ):ℝ)):=by
    intro u; change (1/100:ℝ)=_; exact hconstant.symm
  have hp:(ρ*(1/100)/2)*D=(1/100)*Fintype.card U:=by
    calc
      _ = (1/100:ℝ)*(ρ*D)/2 := by ring
      _ = _ := by rw [hsize]; ring
  have hk:(ρ*((1/100)/(((r+4):ℕ):ℝ))/2)*D=
      ((1/100)/(((r+4):ℕ):ℝ))*Fintype.card U:=by
    calc
      _ = ((1/100)/(((r+4):ℕ):ℝ))*(ρ*D)/2 := by ring
      _ = _ := by rw [hsize]; ring
  have hstats':MarkedReferenceStatistics (P.comap F₀) πW d false false D ε δ γ
      (ρ*(1/100)/2) (ρ*((1/100)/(((r+4):ℕ):ℝ))/2) (1/100)
      ((1/100)/(((r+4):ℕ):ℝ)) (markedRetainedPairRestriction f uEq π πW hc d false z).1:=hstats
  have ht:=marked_relabelled_reference_neighbourhood_global_balance F₀ f hf uEq P π πW hc d h (r+4) hh
    false false D ε δ γ (ρ*(1/100)/2) (ρ*((1/100)/(((r+4):ℕ):ℝ))/2)
    (1/100) ((1/100)/(((r+4):ℕ):ℝ)) errR errI η
    (longAssignedIntervalProbability F hF K (r+4) θ) (longAssignedSpokeProbability F hF K (r+4) θ)
    false z H hq (by intro u; rfl) hp hk hconstant.symm hstats' hrows hindices
    (by simpa only [Fintype.card_fin] using hbudget)
    (by simpa only [Fintype.card_fin] using hmarked)
    (by simpa only [Fintype.card_fin] using hcolumn)
  simpa only [Fintype.card_fin] using ht
end Oberwolfach
