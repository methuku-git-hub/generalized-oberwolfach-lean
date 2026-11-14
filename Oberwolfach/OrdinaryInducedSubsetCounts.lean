module

public import Oberwolfach.InducedSetEmbedding

@[expose] public section
/-! A subset inside an induced host has exactly its ambient cardinality
    and ambient neighborhood counts, including roots outside the subset. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem ordinary_induced_subset_counts (P:SimpleGraph V) (C A:Finset V) (hAC:A⊆C):
    let Ain:=A.subtype (fun v=>v∈C);
    Ain.card=A.card ∧
      ∀x:{v:V // v∈C},
        (Ain∩(P.induce (C:Set V)).neighborFinset x).card=(A∩P.neighborFinset x.val).card:=by
  intro Ain
  have himg:Ain.map (Function.Embedding.subtype (fun v=>v∈C))=A:=
    Finset.subtype_map_of_mem (fun x hx=>hAC hx)
  have hcard:Ain.card=A.card:=by rw [←himg,Finset.card_map]
  refine ⟨hcard,?_⟩
  intro x
  let T:FixedSubset {v:V // v∈C} A.card:=⟨Ain,hcard⟩
  have hh:=inducedSetEmbedding_degree P C T x
  change ((P.induce (C:Set V)).neighborFinset x∩Ain).card=
    (P.neighborFinset x.val∩Ain.map (Function.Embedding.subtype (fun v=>v∈C))).card at hh
  rw [himg] at hh
  rw [Finset.inter_comm ((P.induce (C:Set V)).neighborFinset x) Ain] at hh
  rw [Finset.inter_comm (P.neighborFinset x.val) A] at hh
  exact hh
end Oberwolfach
