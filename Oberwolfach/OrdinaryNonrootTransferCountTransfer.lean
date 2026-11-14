module

public import Oberwolfach.OrdinaryInducedTransferEmbedding
public import Oberwolfach.OrdinaryNonrootTransferCounts
public import Oberwolfach.FiniteConfigurationLoss

@[expose] public section
/-! Transfer configurations survive restriction to any outcome-dependent
nonroot domain, with an explicit count loss. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]

theorem ordinary_nonroot_transfer_count_transfer
    (Q F:SimpleGraph V) (H:V→U→Prop) (r:ℕ) (hr:3≤r)
    (T:Finset V) (W:Finset U):
    let A:=Finset.univ\T;let B:=Finset.univ\W;
    ∀(v:A) (u u':B),
    (Fintype.card (OrdinaryTransferConfiguration hr Q F H v.val u.val u'.val):ℝ)-
      Fintype.card (OrdinaryTransferConfiguration hr (Q.induce (A:Set V)) (F.induce (A:Set V))
        (fun (z:A) (h:B)=>H z.val h.val) v u u')≤
        (T.card:ℝ)*(r:ℝ)^2*(Fintype.card V:ℝ)^(r^2-1):=by
  intro A B v u u'
  let good:=fun C:OrdinaryTransferConfiguration hr Q F H v.val u.val u'.val=>Set.range C.labels⊆A
  have hl:=finite_configuration_loss good (ordinaryInducedTransfer Q F H A B r hr v u u')
    (ordinary_induced_transfer_injective Q F H A B r hr v u u')
  have hf (C:OrdinaryTransferConfiguration hr Q F H v.val u.val u'.val):
      (if good C then (0:ℝ) else 1)=if ∃z∈T,z∈Set.range C.labels then 1 else 0:=by
    have he:¬good C ↔ ∃z∈T,z∈Set.range C.labels:=by
      simp only [good,A,Set.subset_def,Finset.mem_coe,Finset.mem_sdiff,Finset.mem_univ,true_and]
      push_neg
      tauto
    by_cases hg:good C
    · have hn:¬(∃z∈T,z∈Set.range C.labels):=fun hh=>(he.mpr hh) hg
      rw [if_pos hg,if_neg hn]
    · have hh:=he.mp hg
      rw [if_neg hg,if_pos hh]
  calc
    _ ≤ ∑ C:OrdinaryTransferConfiguration hr Q F H v.val u.val u'.val,if good C then (0:ℝ) else 1:=by
      convert hl using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
    _ = ∑ C:OrdinaryTransferConfiguration hr Q F H v.val u.val u'.val,
        if ∃z∈T,z∈Set.range C.labels then (1:ℝ) else 0:=Finset.sum_congr rfl (fun C _=>hf C)
    _ ≤ _:=by
      convert ordinary_transfer_excluded_vertices_loss (hr:=hr) (Q:=Q) (F:=F) (H:=H)
        (v:=v.val) (u:=u.val) (u':=u'.val) T using 1 <;>
        congr! 10 <;> exact Subsingleton.elim _ _
end Oberwolfach
