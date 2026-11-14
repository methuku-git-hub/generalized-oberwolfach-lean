module

public import Oberwolfach.MarkedFiniteInducedDomainBalance

@[expose] public section

/-! Quantitative balance after the sparse inner correction. The input
balance is evaluated in the original graph on the original deeper domains;
the correction contributes its actual finite incidences. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

theorem marked_finite_corrected_inner_domain_bound
    (tail head:E→V) (ktail khead:K→V) (HK:V→U→Prop)
    (A DA:Finset (E⊕K)) (S DS:Finset (V×U)) (m:ℕ)
    (I T:Finset V) (J W:Finset U) (hT:T⊆I) (hW:W⊆J)
    (hDA:DA⊆A.filter (fun a=>Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I))
    (hDS:DS⊆S.filter (fun s=>s.1∈I∧s.2∈J))
    (ε δ:ℝ) (hδ:0≤δ)
    (hA:∀ v,((DA.filter (fun a=>Sum.elim tail ktail a=v∨Sum.elim head khead a=v)).card:ℝ)≤δ)
    (hR:∀ v,((DS.filter (fun s=>s.1=v)).card:ℝ)≤δ)
    (hC:∀ u,((DS.filter (fun s=>s.2=u)).card:ℝ)≤δ)
    (z:V⊕U) (hz:Sum.elim (fun v=>v∈I) (fun u=>u∈J) z) (i:Fin 4)
    (hbalance:|markedFiniteDomainBalance tail head ktail khead HK A S m T W z i|≤ε):
    |markedFiniteDomainBalance tail head ktail khead HK
      ((A.filter (fun a=>Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I))\DA)
      ((S.filter (fun s=>s.1∈I∧s.2∈J))\DS) m T W z i|≤ε+(m+2)*δ:=by
  rw [markedFiniteDomainBalance_sdiff _ _ _ _ _ _ _ _ _ _ _ _ hDA hDS,
    markedFiniteDomainBalance_induced_inside _ _ _ _ _ _ _ _ I T J W hT hW z hz]
  exact (abs_sub _ _).trans (add_le_add hbalance
    (markedFiniteDomainBalance_bound tail head ktail khead HK DA DS m T W δ hδ hA hR hC z i))

end Oberwolfach
