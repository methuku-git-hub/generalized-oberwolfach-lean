module

public import Oberwolfach.ResidualGlobalMarkerSet
public import Oberwolfach.ResidualPrescribedMarkerFamilyCount
public import Oberwolfach.TwoFactorPrescribedMarkersIndependent

@[expose] public section
/-! Independence, exact cardinality and survival of the prescribed set for
the actual extended-path and global-deletion construction. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V I:Type} [Fintype V] [DecidableEq V] [DecidableEq I]

theorem residual_actual_prescribed_set (F Q:SimpleGraph V)
    (hF:F.IsRegularOfDegree 2) (hQ:Q≤F)
    (s₁ s₂:Finset I) (hs:Disjoint s₁ s₂)
    (u v:I→V) (P:∀i,F.Walk (u i) (v i))
    (hp:∀i∈s₁∪s₂,(P i).IsPath)
    (hP:(↑(s₁∪s₂):Set I).PairwiseDisjoint (fun i=>(P i).support.toFinset))
    (c d:ℕ) (hc:3≤c) (hd:0<d) (hlen:∀i∈s₁∪s₂,(P i).length=c*d+4)
    (T:I→Finset ℕ) (hT:∀i,T i⊆Finset.range d) (C:Finset V)
    (hC:∀i∈s₁∪s₂,Disjoint (P i).support.toFinset C):
    let R:=Finset.univ \ (C ∪ (s₁∪s₂).biUnion (pathFamilyLocalDeletion F s₁ u v P c d T hT))
    let A₀ := (s₁.biUnion (fun i=>{(P i).getVert 2,(P i).getVert (2+c*d)})) ∪
      (R ∩ s₂.biUnion (fun i=>(Finset.range (d+1)).image (fun j=>(P i).getVert (2+c*j))))
    let missing:=∑i∈s₂,(d-(T i).card)
    let runs:=∑i∈s₂,(selectedSegmentRuns d (T i)).card;
    A₀⊆R ∧ (∀ x∈A₀,∀ y∈A₀,¬Q.Adj x y) ∧
      A₀.card=2*s₁.card+s₂.card+missing+runs := by
  let s:=s₁∪s₂
  let D:=pathFamilyLocalDeletion F s₁ u v P c d T hT
  let R:=Finset.univ \ (C∪s.biUnion D)
  let A₁:=s₁.biUnion (fun i=>{(P i).getVert 2,(P i).getVert (2+c*d)})
  let M:=s₂.biUnion (fun i=>(Finset.range (d+1)).image (fun j=>(P i).getVert (2+c*j)))
  let A₀:=A₁∪(R∩M)
  have hD:∀i∈s,D i⊆(P i).support.toFinset := by
    intro i hi
    exact path_family_local_deletion_subset F s₁ u v P c d T hT i (hlen i hi)
  have hA₁:A₁⊆R := by
    intro x hx
    obtain ⟨i,hi,hx⟩:=Finset.mem_biUnion.mp hx
    have hi':i∈s := Finset.mem_union_left _ hi
    have hxin:x∈(P i).support.toFinset := by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl|rfl <;> simp
    have hnot:x∉D i := by
      simp only [D,pathFamilyLocalDeletion,hi,ite_true,centralPathInterior,Finset.mem_sdiff]
      intro h
      exact h.2 hx
    have hloc:=disjoint_family_deletion_localization s (fun k=>(P k).support.toFinset)
      D C hP hD hC i hi' x hxin
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hloc.2 hnot⟩
  have hA₀:A₀⊆R := Finset.union_subset hA₁ Finset.inter_subset_left
  have hind:=two_factor_residual_prescribed_markers_independent F Q hF hQ s₁ s₂ u v P hp hP c d hc hlen R
  have hset:=selected_marker_global_set_identity F s₁ s₂ hs u v P hp hP c d (by omega) hlen T hT C hC
  have hcount:=residual_prescribed_marker_family_count F s₁ s₂ hs u v P hp hP c d (by omega) hd hlen T (by intro i hi;exact hT i)
  dsimp only at hset hcount hind ⊢
  refine ⟨hA₀,hind,?_⟩
  change (A₁∪(R∩M)).card=2*s₁.card+s₂.card+
    (∑i∈s₂,(d-(T i).card))+(∑i∈s₂,(selectedSegmentRuns d (T i)).card)
  rw [hset]
  exact hcount
end Oberwolfach
