module

public import Oberwolfach.ResidualMarkerFamilyCard
public import Oberwolfach.ResidualRunFamilyCounts

@[expose] public section
/-! Count prescribed endpoints and surviving selected-path markers across
vertex-disjoint extended paths. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V I:Type} [Fintype V] [DecidableEq V] [DecidableEq I]

theorem residual_prescribed_marker_family_count (F:SimpleGraph V)
    (s₁ s₂:Finset I) (hs:Disjoint s₁ s₂)
    (u v:I→V) (P:∀i,F.Walk (u i) (v i))
    (hp:∀i∈s₁∪s₂,(P i).IsPath)
    (hP:(↑(s₁∪s₂):Set I).PairwiseDisjoint (fun i=>(P i).support.toFinset))
    (c d:ℕ) (hc:0<c) (hd:0<d) (hlen:∀i∈s₁∪s₂,(P i).length=c*d+4)
    (T:I→Finset ℕ) (hT:∀i∈s₂,T i⊆Finset.range d):
    let A₁:=s₁.biUnion (fun i=>{(P i).getVert 2,(P i).getVert (2+c*d)})
    let A₂:=s₂.biUnion (fun i=>(survivingSegmentMarkers d (T i)).image
      (fun j=>(P i).getVert (2+c*j)))
    let missing:=∑i∈s₂,(d-(T i).card)
    let runs:=∑i∈s₂,(selectedSegmentRuns d (T i)).card;
    (A₁∪A₂).card=2*s₁.card+s₂.card+missing+runs := by
  let s:=s₁∪s₂
  let A₁:=s₁.biUnion (fun i=>{(P i).getVert 2,(P i).getVert (2+c*d)})
  let A₂:=s₂.biUnion (fun i=>(survivingSegmentMarkers d (T i)).image
      (fun j=>(P i).getVert (2+c*j)))
  have hdisj:Disjoint A₁ A₂ := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨i,hi,hx⟩:=Finset.mem_biUnion.mp hx
    obtain ⟨j,hj,hy⟩:=Finset.mem_biUnion.mp hy
    have hij:i≠j := by
      intro h;subst j
      exact Finset.disjoint_left.mp hs hi hj
    have hxi:x∈(P i).support.toFinset := by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl|rfl <;> simp
    obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp hy
    have hxj:(P j).getVert (2+c*k)∈(P j).support.toFinset := by simp
    exact Finset.disjoint_left.mp (hP (Finset.mem_union_left _ hi) (Finset.mem_union_right _ hj) hij) hxi hxj
  have hP₁:(↑s₁:Set I).PairwiseDisjoint (fun i=>(P i).support.toFinset) := by
    intro i hi j hj hij
    exact hP (Finset.mem_union_left _ hi) (Finset.mem_union_left _ hj) hij
  have hP₂:(↑s₂:Set I).PairwiseDisjoint (fun i=>(P i).support.toFinset) := by
    intro i hi j hj hij
    exact hP (Finset.mem_union_right _ hi) (Finset.mem_union_right _ hj) hij
  have h₁:=extended_path_marker_family_card F s₁ u v P
    (fun i hi=>hp i (Finset.mem_union_left _ hi)) hP₁ c d hc
    (fun i hi=>hlen i (Finset.mem_union_left _ hi)) (fun _=>{0,d})
    (by intro i hi j hj;simp only [Finset.mem_insert,Finset.mem_singleton] at hj;rcases hj with rfl|rfl <;> simp)
  have hA₁:A₁.card=2*s₁.card := by
    have hh:(s₁.biUnion (fun i=>({0,d}:Finset ℕ).image (fun j=>(P i).getVert (2+c*j)))).card=2*s₁.card := by
      rw [h₁]
      have h0d:(0:ℕ)≠d := by omega
      simp [h0d,mul_comm]
    simpa [A₁] using hh
  have h₂:=extended_path_marker_family_card F s₂ u v P
    (fun i hi=>hp i (Finset.mem_union_right _ hi)) hP₂ c d hc
    (fun i hi=>hlen i (Finset.mem_union_right _ hi))
    (fun i=>survivingSegmentMarkers d (T i))
    (by intro i hi;exact Finset.sdiff_subset)
  have hA₂:A₂.card=∑i∈s₂,(survivingSegmentMarkers d (T i)).card := h₂
  have hsum:=(maximal_run_family_counts s₂ d hd T hT).1
  change (A₁∪A₂).card=2*s₁.card+s₂.card+
    (∑i∈s₂,(d-(T i).card))+(∑i∈s₂,(selectedSegmentRuns d (T i)).card)
  rw [Finset.card_union_of_disjoint hdisj,hA₁,hA₂,hsum]
  omega
end Oberwolfach
