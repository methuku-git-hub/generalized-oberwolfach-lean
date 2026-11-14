module

public import Oberwolfach.EndpointPotentialEstimates
public import Oberwolfach.EndpointConflictRestriction
public import Oberwolfach.EndpointConflictDeletion
public import Oberwolfach.EndpointSpokeDomain
public import Oberwolfach.EndpointPotentialDeletionBounds

@[expose] public section

/-! The same fixed-weight event controls every later bounded deletion.
The sampling conflict graph is restricted to the rim/root domain, so hubs
are isolated in the conflict graph used by the endpoint factor theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V Γ Color:Type} [Fintype V] [Fintype Γ] [Fintype Color] [DecidableEq V]

theorem endpoint_potential_estimates_after_deletion (P F:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (A B X Y:Finset V) (hA:0<A.card) (hBA:B.card≤A.card) (hAY:A⊆Y) (hXY:X⊆Y) (hYB:Disjoint Y B)
    (p₀ pR pH ω C t:ℝ) (hp₀:0<p₀) (hpR:p₀≤pR) (hpH:p₀≤pH) (hω:0<ω) (hC:0<C)
    (hB:ω*A.card≤(B.card:ℝ)) (j:Color) (weight:V→Sym2 V→ℝ)
    (hw:∀ x∈X,∀ e∈(endpointEligibleGraph P F (A∩P.neighborFinset x) x).edgeSet,
      0≤weight x e∧weight x e≤C/A.card)
    (σ:RawWheelOutcome V V Γ Color)
    (hpot:EndpointPotentialEstimates P F π d A B X pR pH j weight t σ):
    let F₀:=spanningRestriction F Y
    let R:=rawWheelGraph P σ\F
    let H:=bipartiteRelationGraph Y B hYB (rawWheelSpokes π d σ j)
    ∀ (D E:SimpleGraph V) (L:ℝ),0≤L →
      (∀ v,(D.degree v:ℝ)≤L) → (∀ v,(E.degree v:ℝ)≤L) →
    ∀ x∈X,
      (∀ v∈common A {x} (fun z=>(P\F₀).neighborFinset z),
        |endpointRowPotential P (R\D) (H\E) F₀ A B x v (weight x) (B.card*pR^2*pH^3)-
          endpointEligibleRowWeight F₀ (A∩P.neighborFinset x) x v (fun v w=>weight x s(v,w))|≤
          t+5*(C/(ω*p₀^5))*L/A.card) ∧
      (∀ u∈B,|endpointIndexPotential P (R\D) (H\E) F₀ A x u (weight x) (B.card*pR^2*pH^3)-
          pR/(B.card*pH)*(∑ e∈(endpointEligibleGraph P F₀ (A∩P.neighborFinset x) x).edgeFinset,weight x e)|≤
          t+3*(C/(ω*p₀^5))*L/A.card):=by
  dsimp only
  intro D E L hL hD hE x hx
  let F₀:=spanningRestriction F Y
  let R:=rawWheelGraph P σ\F
  let H:=bipartiteRelationGraph Y B hYB (rawWheelSpokes π d σ j)
  have hxy:x∈Y:=hXY hx
  have hAB:Disjoint (insert x A) B:=hYB.mono_left (Finset.insert_subset hxy hAY)
  have hbase:=hpot x hx hAB
  have hspoke:=endpoint_potentials_on_larger_spoke_domain P (rawWheelGraph P σ) F
    (rawWheelSpokes π d σ j) A B Y x hAY hxy hYB (weight x) (B.card*pR^2*pH^3)
  have hdel:=endpoint_potentials_conflict_deletion P (rawWheelGraph P σ) H F A B x (weight x) (B.card*pR^2*pH^3)
  have hrestrict:=endpoint_potentials_conflict_restriction P R H F A B Y x hAY hxy (weight x) (B.card*pR^2*pH^3)
  have hel:=endpoint_eligible_graph_conflict_restriction P F (A∩P.neighborFinset x) Y x
    (Finset.inter_subset_left.trans hAY) hxy
  have hroot:=common_conflict_restriction P F A {x} Y hAY (Finset.singleton_subset_iff.mpr hxy)
  have hrow:∀ v∈common A {x} (fun z=>(P\F₀).neighborFinset z),
      |endpointRowPotential P R H F₀ A B x v (weight x) (B.card*pR^2*pH^3)-
        endpointEligibleRowWeight F₀ (A∩P.neighborFinset x) x v (fun v w=>weight x s(v,w))|≤t:=by
    intro v hv
    have hvA:v∈A:=((mem_common_iff A {x} (fun z=>(P\F₀).neighborFinset z) v).mp hv).1
    have hv':v∈common A {x} (fun z=>(P\F).neighborFinset z):=by rw [←hroot];exact hv
    have htarget:=endpoint_row_target_conflict_restriction F (A∩P.neighborFinset x) Y x v
      (Finset.inter_subset_left.trans hAY) hxy (hAY hvA) (fun v w=>weight x s(v,w))
    rw [hrestrict.1 v,htarget,hdel.1 v,hspoke.1 v]
    exact (hbase.1 v hv').le
  have hindex:∀ u∈B,|endpointIndexPotential P R H F₀ A x u (weight x) (B.card*pR^2*pH^3)-
      pR/(B.card*pH)*(∑ e∈(endpointEligibleGraph P F₀ (A∩P.neighborFinset x) x).edgeFinset,weight x e)|≤t:=by
    intro u hu
    rw [hrestrict.2 u,hel,hdel.2 u,hspoke.2 u hu]
    exact (hbase.2 u hu).le
  have ha:(0:ℝ)<A.card:=Nat.cast_pos.mpr hA
  have hb:(0:ℝ)<B.card:=(mul_pos hω ha).trans_le hB
  have hpR0:0<pR:=hp₀.trans_le hpR
  have hpH0:0<pH:=hp₀.trans_le hpH
  have hpow:p₀^5≤pR^2*pH^3:=by
    have hh:=mul_le_mul (pow_le_pow_left₀ hp₀.le hpR 2) (pow_le_pow_left₀ hp₀.le hpH 3)
      (pow_nonneg hp₀.le 3) (pow_nonneg hpR0.le 2)
    nlinarith only [hh]
  have hcoef:∀ e∈(endpointEligibleGraph P F₀ (A∩P.neighborFinset x) x).edgeSet,
      0≤weight x e/(B.card*pR^2*pH^3) ∧ weight x e/(B.card*pR^2*pH^3)≤(C/(ω*p₀^5))/(A.card:ℝ)^2:=by
    intro e he
    rw [hel] at he
    have hwe:=hw x hx e he
    refine ⟨div_nonneg hwe.1 (by positivity),?_⟩
    calc
      _≤(C/A.card)/(B.card*pR^2*pH^3):=div_le_div_of_nonneg_right hwe.2 (by positivity)
      _≤(C/A.card)/((ω*A.card)*p₀^5):=div_le_div_of_nonneg_left (by positivity) (by positivity) (by
        have hh:=mul_le_mul hB hpow (pow_nonneg hp₀.le 5) hb.le
        simpa only [mul_assoc] using hh)
      _=_:=by field_simp <;> ring
  exact endpoint_potential_errors_after_deletion P R H F₀ D E A B
    (common A {x} (fun z=>(P\F₀).neighborFinset z)) x (weight x)
    (fun v=>endpointEligibleRowWeight F₀ (A∩P.neighborFinset x) x v (fun v w=>weight x s(v,w)))
    (fun _=>pR/(B.card*pH)*(∑ e∈(endpointEligibleGraph P F₀ (A∩P.neighborFinset x) x).edgeFinset,weight x e))
    (B.card*pR^2*pH^3) (C/(ω*p₀^5)) L t hA hBA (by positivity) hL hcoef hD hE hrow hindex

end Oberwolfach
