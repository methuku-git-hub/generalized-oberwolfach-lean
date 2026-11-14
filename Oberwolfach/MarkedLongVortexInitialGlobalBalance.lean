module

public import Oberwolfach.MarkedLongAssignedRelabelledGlobalBalance
public import Oberwolfach.MarkedVortexInitialExtendedEquivs

@[expose] public section
/-! Apply the global correction balance estimates to the actual level-zero
vortex reference statistics and the same host-level retained sample. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_long_assigned_vortex_initial_global_balance
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (hn:1≤n) (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (Dnat vsize:ℕ) (βQ εQ:ℝ) (Q:Vortex U P Dnat βQ εQ vsize)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d h r K:ℕ) (hh:1≤h)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (θ D ρ ε δ γ errR errI η:ℝ)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Bool) π d false) (H:Bool→Fin n→U→Prop)
    (hsize:ρ*D=2*Fintype.card U)
    (hstats:MarkedReferenceStatistics (P.comap (markedVortexVertexEmbedding Q 0))
      (markedVortexPermutation Q π hpres 0) d false false D ε δ γ
      (ρ*(1/100)/2) (ρ*((1/100)/(((r+4):ℕ):ℝ))/2)
      (1/100) ((1/100)/(((r+4):ℕ):ℝ))
      (rawMarkedRestrictPair (markedVortexVertexEmbedding Q 0) (markedVortexHubEmbedding Q 0) z.1))
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
  let f:=markedVortexInitialExtendedVertexEquiv Q
  let uEq:=markedVortexInitialExtendedHubEquiv Q
  letI:Nonempty (markedVortexVertexType Q 0):=⟨f.symm (Classical.choice inferInstance)⟩
  let πW:=markedVortexPermutation Q π hpres 0
  have hf:∀w,f w=markedVortexVertexEmbedding Q 0 w:=by intro w;rfl
  have hc:∀w,f (πW w)=π (f w):=marked_vortex_initial_extended_equiv_commutes Q π hpres
  have hstats':MarkedReferenceStatistics (P.comap (markedVortexVertexEmbedding Q 0)) πW d false false D ε δ γ
      (ρ*(1/100)/2) (ρ*((1/100)/(((r+4):ℕ):ℝ))/2)
      (1/100) ((1/100)/(((r+4):ℕ):ℝ))
      (markedRetainedPairRestriction f uEq π πW hc d false z).1:=by
    convert hstats using 1
    rfl
  exact marked_long_assigned_relabelled_reference_global_balance
    (markedVortexVertexEmbedding Q 0) f hf uEq P π πW hc d h r K hh F hF
    θ D ρ ε δ γ errR errI η z H hsize hstats' hrows hindices hbudget hmarked hcolumn
end Oberwolfach
