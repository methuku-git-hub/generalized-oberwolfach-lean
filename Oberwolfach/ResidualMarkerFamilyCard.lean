module

public import Oberwolfach.ResidualMarkerInjection

@[expose] public section
/-! Count distinct marked vertices across disjoint extended source paths. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V I:Type} [Fintype V] [DecidableEq V] [DecidableEq I]

theorem extended_path_marker_family_card (F:SimpleGraph V) (s:Finset I)
    (u v:I→V) (P:∀i,F.Walk (u i) (v i))
    (hp:∀i∈s,(P i).IsPath)
    (hP:(↑s:Set I).PairwiseDisjoint (fun i=>(P i).support.toFinset))
    (c d:ℕ) (hc:0<c) (hlen:∀i∈s,(P i).length=c*d+4)
    (T:I→Finset ℕ) (hT:∀i∈s,T i⊆Finset.range (d+1)):
    (s.biUnion (fun i=>(T i).image (fun j=>(P i).getVert (2+c*j)))).card =
      ∑ i∈s,(T i).card := by
  have hdisj:(↑s:Set I).PairwiseDisjoint
      (fun i=>(T i).image (fun j=>(P i).getVert (2+c*j))) := by
    intro i hi j hj hij
    apply (hP hi hj hij).mono
    · intro x hx
      obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hx
      exact List.mem_toFinset.mpr ((P i).getVert_mem_support _)
    · intro x hx
      obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp hx
      exact List.mem_toFinset.mpr ((P j).getVert_mem_support _)
  rw [Finset.card_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro i hi
  exact extended_path_marker_image_card (P i) (hp i hi) c d hc (hlen i hi) (T i) (hT i hi)
end Oberwolfach
