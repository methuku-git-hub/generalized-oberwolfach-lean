module

public import Oberwolfach.MarkedOrdinaryResourceLoads
public import Oberwolfach.OrderedOrdinaryPairBound

@[expose] public section
/-! The ordinary candidate codegree bound remains valid on the whole
marked typed resource universe, with zero outside its image. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
  {m b:ℕ} {π:Equiv.Perm V}

theorem resource_omitted_pair_weight_symm_general {A C:Type} [Fintype A] [Fintype C] [DecidableEq A]
    (R:C→Finset A) (w:C→ℝ) (e f:A):
    resourceOmittedPairWeight R w e f=resourceOmittedPairWeight R w f e := by
  unfold resourceOmittedPairWeight
  apply Finset.sum_congr rfl
  intro c _
  by_cases h:e=f
  · subst f;simp
  · by_cases he:e∈R c <;> by_cases hf:f∈R c <;> simp [h,Ne.symm h,he,hf]

theorem embedded_ordered_ordinary_pair_bound
    (hm:2≤m) (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (w:OrderedOrdinaryWheel (U:=U) π b (m+1)→ℝ) (B:ℝ) (hB:0≤B)
    (hw:∀W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
    (e f:((V×V)⊕(V×V))⊕(Bool×V×U)):
    resourceOmittedPairWeight (fun W=>(orderedOrdinaryResources W).map ordinaryMarkedResourceEmbedding) w e f≤
      ((m:ℝ)+1)^3*B/(Fintype.card V:ℝ) := by
  by_cases he:∃a,ordinaryMarkedResourceEmbedding a=e
  · obtain ⟨a,rfl⟩:=he
    by_cases hf:∃b,ordinaryMarkedResourceEmbedding b=f
    · obtain ⟨b,rfl⟩:=hf
      rw [resource_omitted_pair_weight_map]
      exact orderedOrdinary_omitted_pair_bound hm hn hu w B hB hw a b
    · rw [resource_omitted_pair_weight_symm_general]
      rw [resource_omitted_pair_weight_map_outside _ _ _ _ _ (fun x h=>hf ⟨x,h⟩)]
      positivity
  · rw [resource_omitted_pair_weight_map_outside _ _ _ _ _ (fun x h=>he ⟨x,h⟩)]
    positivity
end Oberwolfach
