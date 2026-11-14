module

public import Oberwolfach.SparseIntersectionData

@[expose] public section

/-! Conversion of the manuscript's fixed spoke-density intersection
estimates to the inverse-density profiles used by alternating correction. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {A B : Type*} [Fintype A] [Fintype B]

def commonSpokeNeighbours (H : A → B → Prop) (S : Finset B) : Finset A :=
  Finset.univ.filter (fun x=>∀ u∈S,H x u)

theorem commonSpokeNeighbours_singleton (H : A → B → Prop) (u : B) :
    ((commonSpokeNeighbours H {u}).card:ℝ)=bipColumnDegree H u := by
  classical
  simp only [commonSpokeNeighbours,Finset.mem_singleton,forall_eq,bipColumnDegree,bipAdj]
  simp

theorem commonSpokeNeighbours_pair (H : A → B → Prop) (u v : B) :
    ((commonSpokeNeighbours H {u,v}).card:ℝ)=bipPairIntersection H u v := by
  classical
  rw [commonSpokeNeighbours,Finset.card_filter]
  push_cast
  unfold bipPairIntersection
  apply Finset.sum_congr rfl
  intro x _
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  unfold bipAdj
  split_ifs <;> simp_all

theorem commonSpokeNeighbours_triple (H : A → B → Prop) (u v t : B) :
    ((commonSpokeNeighbours H {u,v,t}).card:ℝ)=bipTripleIntersection H u v t := by
  classical
  rw [commonSpokeNeighbours,Finset.card_filter]
  push_cast
  unfold bipTripleIntersection
  apply Finset.sum_congr rfl
  intro x _
  simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq]
  unfold bipAdj
  split_ifs <;> simp_all

theorem bipWeightedCodegree_constant (H : A → B → Prop) (p : ℝ) (x y : A) :
    bipWeightedCodegree H (fun _=>1/p) x y=
      ((Finset.univ.filter (fun u=>H x u ∧ H y u)).card:ℝ)/p^2 := by
  classical
  unfold bipWeightedCodegree
  rw [Finset.card_filter]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro u _
  unfold bipAdj
  split_ifs <;> simp_all

theorem sparseIntersectionData_of_constant_density
    (H : A → B → Prop) (p p₀ δ D : ℝ) (hp₀ : 0<p₀) (hp : p₀≤p) (hp1 : p≤1)
    (hδ : 0≤δ) (hD : 0≤D)
    (hinter : ∀ S : Finset B,1≤S.card → S.card≤3 →
      |((commonSpokeNeighbours H S).card:ℝ)-p^S.card*Fintype.card A|≤δ*Fintype.card A)
    (hcodeg : ∀ x,∃ E : Finset A,(E.card:ℝ)≤D ∧ ∀ y,y∉E →
      |((Finset.univ.filter (fun u=>H x u ∧ H y u)).card:ℝ)-p^2*Fintype.card B|≤
        δ*p^2*Fintype.card B) :
    SparseIntersectionData H (fun _=>p) (fun _=>1/p) (max 1 (1/p₀)) δ D := by
  classical
  have hp0 : 0<p := lt_of_lt_of_le hp₀ hp
  have hp2 : 0<p^2 := sq_pos_of_pos hp0
  refine ⟨le_max_left _ _,hδ,hD,fun _=>⟨hp0.le,hp1⟩,?_,?_,?_,?_,?_,?_⟩
  · intro u
    exact ⟨by positivity,le_trans (one_div_le_one_div_of_le hp₀ hp) (le_max_right _ _)⟩
  · intro u
    exact one_div_mul_cancel (ne_of_gt hp0)
  · intro u
    have hh := hinter {u} (by simp) (by simp)
    simpa only [Finset.card_singleton,pow_one,commonSpokeNeighbours_singleton,mul_comm p] using hh
  · intro u v huv
    have hh := hinter {v,u} (by simp [Ne.symm huv]) (by simp [Ne.symm huv])
    have hc : ({v,u}:Finset B).card=2 := by simp [Ne.symm huv]
    rw [hc,commonSpokeNeighbours_pair] at hh
    convert hh using 1 <;> ring
  · intro u v t huv hut hvt
    have hc : ({u,v,t}:Finset B).card=3 := by simp [huv,hut,hvt]
    have hh := hinter {u,v,t} (by rw [hc];omega) (by rw [hc])
    rw [hc,commonSpokeNeighbours_triple] at hh
    convert hh using 1 <;> ring
  · intro x
    obtain ⟨E,hE,he⟩ := hcodeg x
    refine ⟨E,hE,?_⟩
    intro y hy
    rw [bipWeightedCodegree_constant]
    have hh := he y hy
    have hid (a b : ℝ) : a/p^2-b=(a-p^2*b)/p^2 := by field_simp <;> ring
    rw [hid,abs_div,abs_of_pos hp2,div_le_iff₀ hp2]
    nlinarith [hh]

end Oberwolfach
