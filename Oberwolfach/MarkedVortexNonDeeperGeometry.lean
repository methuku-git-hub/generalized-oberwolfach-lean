module

public import Oberwolfach.MarkedVortexNextActiveInNonDeeper

@[expose] public section
/-! The next active vertices are exactly the vertices in the next vortex
set outside the deeper set, and the restricted permutations commute. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

def markedVortexNonDeeperPermutation (π:Equiv.Perm V)
    (hπ:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i) (i:ℕ):
    Equiv.Perm (markedVortexNonDeeperVertexType Q i):=
  invariantSetPermutation (markedVortexPermutation Q π hπ i) _ (by
    intro x
    simp only [Finset.mem_coe,Finset.mem_sdiff,Finset.mem_univ,true_and]
    exact not_congr ((marked_vortex_permutation_compatibility Q π hπ i).2.2 x))

theorem marked_vortex_next_active_permutation_commutes (π:Equiv.Perm V)
    (hπ:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i) (i:ℕ)
    (x:↥((Finset.univ\markedVortexInnerVertices Q (i+1)):Finset (markedVortexVertexType Q (i+1)))):
    markedVortexNextActiveInNonDeeper Q i (markedVortexActivePermutation Q π hπ (i+1) x)=
      markedVortexNonDeeperPermutation Q π hπ i (markedVortexNextActiveInNonDeeper Q i x):=by
  apply Subtype.ext
  apply Subtype.ext
  rfl

theorem marked_vortex_next_active_parent_image (i:ℕ):
    (Finset.univ.image (fun x=>markedVortexNonDeeperVertexEmbedding Q i
      (markedVortexNextActiveInNonDeeper Q i x)))=
      markedVortexInnerVertices Q i\markedVortexDeeperVertices Q i:=by
  ext v
  simp only [Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_sdiff]
  constructor
  · rintro ⟨x,rfl⟩
    have hnot: x.val.val∉Q.extendedVertices (i+2):=by
      have hh: x.val∉markedVortexInnerVertices Q (i+1):=(Finset.mem_sdiff.mp x.property).2
      simpa [markedVortexInnerVertices,Nat.add_assoc] using hh
    simp only [markedVortexInnerVertices,markedVortexDeeperVertices,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨x.val.property,hnot⟩
  · rintro ⟨hi,hd⟩
    have hnext:v.val∈Q.extendedVertices (i+1):=by simpa [markedVortexInnerVertices] using hi
    have hdeep:v.val∉Q.extendedVertices (i+2):=by simpa [markedVortexDeeperVertices] using hd
    let x:↥((Finset.univ\markedVortexInnerVertices Q (i+1)):Finset (markedVortexVertexType Q (i+1))):=
      ⟨⟨v.val,hnext⟩,by simp only [Finset.mem_sdiff,Finset.mem_univ,true_and,markedVortexInnerVertices,Finset.mem_filter];simpa [Nat.add_assoc] using hdeep⟩
    refine ⟨x,?_⟩
    apply Subtype.ext
    rfl
end Oberwolfach
