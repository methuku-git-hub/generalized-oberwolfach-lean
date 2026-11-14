module

public import Oberwolfach.OrdinaryFiveGraphGeometry
public import Oberwolfach.PermutationClose

@[expose] public section

/-! Separation in the union of the five diagram row sets. Only the
original roots are omitted from the within-set requirement. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
variable {V:Type} [DecidableEq V]

theorem marked_five_sets_separated (π:Equiv.Perm V) (b:ℕ)
    (L R:Finset V) (T:Fin 3→Finset V) (O:Finset V)
    (hL:∀ v∈L\O,∀ w∈L\O,v≠w→¬PermutationClose π b v w)
    (hR:∀ v∈R,∀ w∈R,v≠w→¬PermutationClose π b v w)
    (hT:∀ i,∀ v∈T i,∀ w∈T i,v≠w→¬PermutationClose π b v w)
    (hLR:∀ v∈L,∀ w∈R,¬PermutationClose π b v w)
    (hLT:∀ i,∀ v∈L,∀ w∈T i,¬PermutationClose π b v w)
    (hRT:∀ i,∀ v∈R,∀ w∈T i,¬PermutationClose π b v w)
    (hTT:∀ i j,i≠j→∀ v∈T i,∀ w∈T j,¬PermutationClose π b v w):
    ∀ v∈ordinaryFiveUnion L R T\O,∀ w∈ordinaryFiveUnion L R T\O,v≠w→¬PermutationClose π b v w:=by
  intro v hv w hw hne
  obtain ⟨hv,hvO⟩:=Finset.mem_sdiff.mp hv
  obtain ⟨hw,hwO⟩:=Finset.mem_sdiff.mp hw
  have cases_mem:∀ x∈ordinaryFiveUnion L R T,x∈L∨x∈R∨∃ i,x∈T i:=by
    intro x hx
    rcases Finset.mem_union.mp hx with hx|hx
    · rcases Finset.mem_union.mp hx with hx|hx
      · exact Or.inl hx
      · exact Or.inr (Or.inl hx)
    · obtain ⟨i,_,hx⟩:=Finset.mem_biUnion.mp hx
      exact Or.inr (Or.inr ⟨i,hx⟩)
  rcases cases_mem v hv with hv|hv|⟨i,hv⟩ <;> rcases cases_mem w hw with hw|hw|⟨j,hw⟩
  · exact hL v (Finset.mem_sdiff.mpr ⟨hv,hvO⟩) w (Finset.mem_sdiff.mpr ⟨hw,hwO⟩) hne
  · exact hLR v hv w hw
  · exact hLT j v hv w hw
  · intro hc;exact hLR w hw v hv ((permutationClose_symm π b _ _).mp hc)
  · exact hR v hv w hw hne
  · exact hRT j v hv w hw
  · intro hc;exact hLT i w hw v hv ((permutationClose_symm π b _ _).mp hc)
  · intro hc;exact hRT i w hw v hv ((permutationClose_symm π b _ _).mp hc)
  · by_cases hij:i=j
    · subst j;exact hT i v hv w hw hne
    · exact hTT i j hij v hv w hw

end Oberwolfach
