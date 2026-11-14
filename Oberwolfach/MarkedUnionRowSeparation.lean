module

public import Oberwolfach.PermutationClose
public import Mathlib.Data.Finset.Union

@[expose] public section

/-! Separation survives adjoining families whose new rows are separated
from the fixed diagram and from every other family's new rows. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V I:Type} [DecidableEq V] [Fintype I]

theorem marked_union_row_separation (π:Equiv.Perm V) (b:ℕ)
    (D O:Finset V) (C:I→Finset V) (hO:O⊆D)
    (hD:∀ v∈D\O,∀ w∈D\O,v≠w→¬PermutationClose π b v w)
    (hDO:∀ v∈D\O,∀ w∈O,¬PermutationClose π b v w)
    (hCD:∀ i,∀ v∈C i\D,∀ w∈D,¬PermutationClose π b v w)
    (hC:∀ i,∀ v∈C i\D,∀ w∈C i\D,v≠w→¬PermutationClose π b v w)
    (hCC:∀ i j,i≠j→∀ v∈C i\D,∀ w∈C j\D,¬PermutationClose π b v w):
    let X:=D∪Finset.univ.biUnion C
    (∀ v∈X\O,∀ w∈X\O,v≠w→¬PermutationClose π b v w)∧
    ∀ v∈X\O,∀ w∈O,¬PermutationClose π b v w:=by
  dsimp only
  have hcases:∀ v∈D∪Finset.univ.biUnion C,v∈D∨∃ i,v∈C i\D:=by
    intro v hv
    by_cases hd:v∈D
    · exact Or.inl hd
    · rcases Finset.mem_union.mp hv with hv|hv
      · exact (hd hv).elim
      · obtain ⟨i,_,hv⟩:=Finset.mem_biUnion.mp hv
        exact Or.inr ⟨i,Finset.mem_sdiff.mpr ⟨hv,hd⟩⟩
  constructor
  · intro v hv w hw hne
    obtain ⟨hv,hvO⟩:=Finset.mem_sdiff.mp hv
    obtain ⟨hw,hwO⟩:=Finset.mem_sdiff.mp hw
    rcases hcases v hv with hv|⟨i,hv⟩ <;> rcases hcases w hw with hw|⟨j,hw⟩
    · exact hD v (Finset.mem_sdiff.mpr ⟨hv,hvO⟩) w (Finset.mem_sdiff.mpr ⟨hw,hwO⟩) hne
    · intro hc;exact hCD j w hw v hv ((permutationClose_symm π b _ _).mp hc)
    · exact hCD i v hv w hw
    · by_cases hij:i=j
      · subst j;exact hC i v hv w hw hne
      · exact hCC i j hij v hv w hw
  · intro v hv w hw
    obtain ⟨hv,hvO⟩:=Finset.mem_sdiff.mp hv
    rcases hcases v hv with hv|⟨i,hv⟩
    · exact hDO v (Finset.mem_sdiff.mpr ⟨hv,hvO⟩) w hw
    · exact hCD i v hv w (hO hw)

end Oberwolfach
