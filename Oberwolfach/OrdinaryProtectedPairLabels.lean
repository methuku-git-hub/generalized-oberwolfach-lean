module

public import Oberwolfach.RawProtectedPairHubLower
public import Oberwolfach.ProtectedPairAllowedEdges

@[expose] public section
/-! The unassigned-pair and start-column tests yield many ordinary protected
list labels for every non-loop physical edge. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_protected_pair_edge_labels
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (π:Equiv.Perm (Fin n)) (d:ℕ) (hd:0<d)
    (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d σ false) t)
    (q:U→Bool→ℝ) (hQ:∀u,∑g,q u g≤1/8) (θ err a:ℝ)
    (hpair:∀x y,x≠y→(5/32:ℝ)*θ^2*Fintype.card U-err≤rawIntervalUnassignedPairColumnCount π d σ x y Finset.univ)
    (hstarts:∀v g,|rawIntervalStartColumnCount π d σ v g Finset.univ-∑u,q u g/(d:ℝ)|<err)
    (hbudget:a*n+5*err≤((5/32:ℝ)*θ^2-1/(4*(d:ℝ)))*Fintype.card U)
    (G:SimpleGraph (Fin n)):
    ∀e∈G.edgeFinset,a*n≤((protectedPairEdgeHubs
      (rawIntervalProtectedUnassignedList π d σ false true t Jret) ∅ e).card:ℝ):=by
  have hh:=raw_protected_pair_hubs_lower_from_counts π d hd σ t Jret q hQ θ err hpair hstarts
  intro e he
  induction e using Sym2.ind with
  | _ x y =>
    have hxy:x≠y:=by
      intro h
      subst y
      exact G.loopless.irrefl x (SimpleGraph.mem_edgeFinset.mp he)
    have hallowed:=protected_pair_edge_hubs_card_lower
      (rawIntervalProtectedUnassignedList π d σ false true t Jret) ∅ x y
    have hc:((rawProtectedPairHubs π d σ false true t Jret x y).card:ℝ)≤
        ((protectedPairEdgeHubs (rawIntervalProtectedUnassignedList π d σ false true t Jret) ∅ s(x,y)).card:ℝ):=by
      have hnat:(rawProtectedPairHubs π d σ false true t Jret x y).card≤
          (protectedPairEdgeHubs (rawIntervalProtectedUnassignedList π d σ false true t Jret) ∅ s(x,y)).card:=by
        simpa only [rawProtectedPairHubs,Finset.card_empty,add_zero] using hallowed
      exact_mod_cast hnat
    linarith [hh x y hxy]
end Oberwolfach
