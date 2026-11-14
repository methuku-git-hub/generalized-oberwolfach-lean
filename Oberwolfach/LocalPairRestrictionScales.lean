module

public import Oberwolfach.CandidateAbsorberGroundRestriction
public import Oberwolfach.PairRestrictionScales

@[expose] public section

/-! Pair-deletion losses measured on the actual local vertex set and
at its supplied scale; the ambient vertex count is irrelevant. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 256
set_option maxHeartbeats 3800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C T : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
    [Fintype T] [DecidableEq T] {c : ℕ}

theorem candidate_absorber_ground_pair_loss_scale (hc : 2 ≤ c) (R : C → Finset V)
    (S : T → VertexAbsorberTemplate c) (X Y : Finset V) (J : ℕ)
    (hJ : ∀ U : Finset V,Fintype.card {C₀ : C // R C₀=U} ≤ J)
    (E : Finset (V×V)) (hE : ∀ e∈E,e.1≠e.2) (d : ℕ)
    (hd : ∀ v∈X,(E.filter (fun e => v=e.1 ∨ v=e.2)).card ≤ d)
    (hsize : E.card ≤ Y.card) (k : ℝ) (hk : 0 ≤ k)
    (hY : (Y.card:ℝ) ≤ c*k) (hX : X.card=c) :
    absorberGroundCount R S X Y ≤
      absorberGroundCount (candidateResourceSet R
        (fun C₀ => ∀ e : E,¬(e.val.1∈R C₀ ∧ e.val.2∈R C₀))) S X Y+
      absorberPairDeletionCoefficient c J (Fintype.card T) d*k^(c*c-1) := by
  have hh := candidate_absorber_ground_bounded_pair_loss hc R S X Y J hJ E hE d hd hsize
  rw [hX] at hh
  push_cast at hh
  apply hh.trans
  apply add_le_add le_rfl
  calc
    _ ≤ ((c*d*(c*c)+(c*c)^2):ℝ)*(Fintype.card T:ℝ)*(c:ℝ)^c*((c:ℝ)*k)^(c*c-1)*(J:ℝ)^(2*c+1) := by
      gcongr
    _ = _ := by
      dsimp [absorberPairDeletionCoefficient]
      push_cast
      rw [mul_pow]
      ring

theorem candidate_resource_induced_pair_degree (R : C → Finset V) (w : C → ℝ)
    (E : Finset (V×V)) (Y : Finset V) (v : V) :
    hypergraphWeightedDegree (candidateResourceSet R
      (fun C₀ => ∀ e : E,¬(e.val.1∈R C₀ ∧ e.val.2∈R C₀)))
      (inducedResourceWeight (candidateResourceSet R
        (fun C₀ => ∀ e : E,¬(e.val.1∈R C₀ ∧ e.val.2∈R C₀))) (fun D => w D.val) Y) v=
      hypergraphWeightedDegree R (pairRestrictedResourceWeight R (inducedResourceWeight R w Y) E) v := by
  let P := fun C₀ => ∀ e : E,¬(e.val.1∈R C₀ ∧ e.val.2∈R C₀)
  change hypergraphWeightedDegree (candidateResourceSet R P)
    (fun D => inducedResourceWeight R w Y D.val) v=_
  convert candidate_resource_degree R P (inducedResourceWeight R w Y) v using 1 <;> congr!

theorem candidate_resource_local_pair_degree_loss_scale (R : C → Finset V) (c J : ℕ) (hc : 3 ≤ c)
    (hR : ∀ C₀,(R C₀).card=c) (hJ : ∀ U : Finset V,Fintype.card {C₀ : C // R C₀=U} ≤ J)
    (w : C → ℝ) (B k u : ℝ) (hB : 0 ≤ B) (hk : 0 < k) (hu : 0 ≤ u)
    (Y : Finset V) (hY : (Y.card:ℝ) ≤ u*k)
    (hw : ∀ C₀,0 ≤ w C₀ ∧ w C₀ ≤ B/k^(c-1))
    (E : Finset (V×V)) (hE : ∀ e∈E,e.1≠e.2) (v : V) (d : ℕ)
    (hd : (E.filter (fun e => v=e.1 ∨ v=e.2)).card ≤ d) (hsize : E.card ≤ Y.card) :
    0 ≤ hypergraphWeightedDegree R (inducedResourceWeight R w Y) v-
      hypergraphWeightedDegree R (pairRestrictedResourceWeight R (inducedResourceWeight R w Y) E) v ∧
    hypergraphWeightedDegree R (inducedResourceWeight R w Y) v-
      hypergraphWeightedDegree R (pairRestrictedResourceWeight R (inducedResourceWeight R w Y) E) v ≤
      (((d:ℝ)+1)*(J:ℝ)*u^(c-2)*B)/k := by
  obtain ⟨hlo,hhi⟩ := resource_bounded_pairs_degree_loss R c J hc hR hJ w (B/k^(c-1))
    (by positivity) hw Y E hE v d hd hsize
  refine ⟨hlo,hhi.trans ?_⟩
  calc
    _ ≤ ((d:ℝ)+1)*(J:ℝ)*(u*k)^(c-2)*(B/k^(c-1)) := by gcongr
    _ = _ := by
      rw [mul_pow]
      have hp : k^(c-1)=k^(c-2)*k := by rw [← pow_succ];congr 1;omega
      rw [hp]
      field_simp

end Oberwolfach
