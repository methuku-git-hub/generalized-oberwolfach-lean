module

public import Oberwolfach.ResidualActualPathFamilyGraph
public import Oberwolfach.ResidualGlobalMarkerSurvival

@[expose] public section
/-! The path-family graph and prescribed-marker construction delete the
same actual path interiors. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V I:Type} [Fintype V] [DecidableEq V] [DecidableEq I]

theorem deleted_path_family_interiors_identity (F:SimpleGraph V)
    (s₁ s₂:Finset I) (hs:Disjoint s₁ s₂) (u v:I→V) (P:∀i,F.Walk (u i) (v i))
    (c d:ℕ) (T:I→Finset ℕ) (hT:∀i,T i⊆Finset.range d):
    let Z:=DeletedPathIndex s₁ s₂ d T
    let U:Z→V:=deletedPathStart F s₁ s₂ u v P c d T
    let W:Z→V:=deletedPathEnd F s₁ s₂ u v P c d T
    let paths:∀z:Z,F.Walk (U z) (W z):=deletedPathWalk F s₁ s₂ u v P c d T (fun i _=>hT i);
    (Finset.univ.biUnion (fun z=>(paths z).support.toFinset \ {U z,W z})) =
      (s₁∪s₂).biUnion (pathFamilyLocalDeletion F s₁ u v P c d T hT) := by
  dsimp only
  ext x
  constructor
  · intro hx
    obtain ⟨z,_,hx⟩:=Finset.mem_biUnion.mp hx
    cases z with
    | inl i =>
      refine Finset.mem_biUnion.mpr ⟨i.1,Finset.mem_union_left _ i.2,?_⟩
      simpa [pathFamilyLocalDeletion,i.2,centralPathInterior,deletedPathWalk,deletedPathStart,deletedPathEnd] using hx
    | inr z =>
      rcases z with ⟨i,r⟩
      have hinot:i.1∉s₁ := by intro h;exact Finset.disjoint_left.mp hs h i.2
      refine Finset.mem_biUnion.mpr ⟨i.1,Finset.mem_union_right _ i.2,?_⟩
      simp only [pathFamilyLocalDeletion,hinot,ite_false]
      apply Finset.mem_biUnion.mpr
      refine ⟨r,by simp,?_⟩
      simpa [deletedPathWalk,deletedPathStart,deletedPathEnd] using hx
  · intro hx
    obtain ⟨i,hi,hx⟩:=Finset.mem_biUnion.mp hx
    by_cases hi₁:i∈s₁
    · let z:DeletedPathIndex s₁ s₂ d T:=.inl ⟨i,hi₁⟩
      refine Finset.mem_biUnion.mpr ⟨z,Finset.mem_univ _,?_⟩
      simpa [z,pathFamilyLocalDeletion,hi₁,centralPathInterior,deletedPathWalk,deletedPathStart,deletedPathEnd] using hx
    · have hi₂:i∈s₂ := by
        rcases Finset.mem_union.mp hi with h|h
        · exact (hi₁ h).elim
        · exact h
      simp only [pathFamilyLocalDeletion,hi₁,ite_false] at hx
      obtain ⟨r,_,hx⟩:=Finset.mem_biUnion.mp hx
      let z:DeletedPathIndex s₁ s₂ d T:=.inr ⟨⟨i,hi₂⟩,r⟩
      refine Finset.mem_biUnion.mpr ⟨z,Finset.mem_univ _,?_⟩
      simpa [z,deletedPathWalk,deletedPathStart,deletedPathEnd] using hx
end Oberwolfach
