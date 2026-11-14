module

public import Oberwolfach.ResourceRootOmittedLoads
public import Oberwolfach.InducedResourceWeights
public import Oberwolfach.AbsorberProfileSampling

@[expose] public section

/-! Local-size alteration estimates for all original roots. Inserting the
root into the ground set is a deterministic representation of an omitted
trial; it does not condition or modify the sampling law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C T:Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
  [Fintype T] [DecidableEq T]

theorem root_omitted_load_induced (R:C→Finset V) (w:C→ℝ) (A:Finset V) (v:V):
    resourceRootOmittedLoad R w (fun x=>x∈A) v=
      hypergraphWeightedDegree R (inducedResourceWeight R w (insert v A)) v:=by
  unfold resourceRootOmittedLoad hypergraphWeightedDegree inducedResourceWeight
  apply Finset.sum_congr rfl
  intro i _
  have he:(∀ x∈R i,x≠v→x∈A)↔R i⊆insert v A:=by
    constructor
    · intro h x hx
      by_cases hxv:x=v
      · simp [hxv]
      · exact Finset.mem_insert_of_mem (h x hx hxv)
    · intro h x hx hxv
      exact (Finset.mem_insert.mp (h hx)).resolve_left hxv
  by_cases hv:v∈R i <;> by_cases hsub:R i⊆insert v A
  all_goals simp [hv,hsub,he]

theorem root_omitted_load_local_change (R:C→Finset V) (c J:ℕ) (hc:2≤c)
    (hR:∀ i,(R i).card=c) (hJ:∀ Y:Finset V,Fintype.card {i:C // R i=Y}≤J)
    (w:C→ℝ) (B:ℝ) (hB:0≤B) (hw:∀ i,0≤w i ∧ w i≤B)
    (A D:Finset V) (v:V):
    |resourceRootOmittedLoad R w (fun x=>x∈A) v-
      resourceRootOmittedLoad R w (fun x=>x∈D) v|≤
      ((A\D).card+(D\A).card:ℕ)*(J:ℝ)*((A∪D).card+1:ℝ)^(c-2)*B:=by
  rw [root_omitted_load_induced,root_omitted_load_induced]
  have hh:=induced_resource_degree_exchange R c J hc hR hJ w B hB hw
    (insert v A) (insert v D) v (Finset.mem_insert_self _ _) (Finset.mem_insert_self _ _)
  have hs (P Q:Finset V):insert v P\insert v Q⊆P\Q:=by
    intro x hx
    have hh:=Finset.mem_sdiff.mp hx
    have hxv:x≠v:=by intro h;subst x;exact hh.2 (Finset.mem_insert_self _ _)
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_insert.mp hh.1).resolve_left hxv,
      fun h=>hh.2 (Finset.mem_insert_of_mem h)⟩
  have hdiff:(((insert v A\insert v D).card+(insert v D\insert v A).card:ℕ):ℝ)≤
      ((A\D).card+(D\A).card:ℕ):=by
    exact_mod_cast Nat.add_le_add (Finset.card_le_card (hs A D)) (Finset.card_le_card (hs D A))
  have hU:((insert v A∪insert v D).card:ℝ)≤(A∪D).card+1:=by
    have he:insert v A∪insert v D=insert v (A∪D):=by ext x;simp
    rw [he]
    exact_mod_cast Finset.card_insert_le v (A∪D)
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul (mul_le_mul_of_nonneg_right hdiff (Nat.cast_nonneg J))
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hU _) (by positivity) (by positivity)) hB)

theorem absorber_ground_local_change {c:ℕ} (R:C→Finset V)
    (S:T→VertexAbsorberTemplate c) (X A D:Finset V) (J:ℕ)
    (hJ:∀ Y:Finset V,Fintype.card {i:C // R i=Y}≤J):
    |absorberGroundCount R S X A-absorberGroundCount R S X D|≤
      ((A\D).card+(D\A).card:ℕ)*
        ((c*c)*Fintype.card T*X.card^c*(A∪D).card^(c*c-1)*J^(2*c+1):ℕ):=by
  exact finite_support_count_difference
    (fun d:LabelledAbsorberFamily R S X=>labelledAbsorberFree R (S d.1) X d.2) A D _
    (labelled_absorber_local_free_vertex_count R S X (A∪D) J hJ)

end Oberwolfach
