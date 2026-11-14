module

public import Oberwolfach.MarkedFiniteResourceSupport
public import Oberwolfach.MarkedFinitePackingIteration

@[expose] public section

/-! A cover-down packing supported outside the remaining inner host
leaves exactly that fixed inner reference minus its newly consumed edges.
The statement uses the actual original arc and spoke complements. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K : Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
    [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

theorem marked_cover_remainder_fixed_inner_complement
    (tail head : E→V) (ktail khead : K→V) (π : Equiv.Perm V)
    (S : Finset (V×U)) (I : Finset V) (J : Finset U) (hI : ∀ v,π v∈I↔v∈I)
    (AR : Finset (E⊕K)) (SR : Finset (V×U)) (hSR : SR⊆S)
    (hA : ∀ a∈AR,Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I)
    (hS : ∀ s∈SR,s.1∈I∧s.2∈J) :
    let B := markedFiniteResources tail head ktail khead π Finset.univ S
    let L := markedFiniteResources tail head ktail khead π AR SR
    let F := B.filter (markedInnerResource I J)\L;
    L⊆B.filter (markedInnerResource I J) ∧ F⊆B.filter (markedInnerResource I J) ∧
    L=B.filter (markedInnerResource I J)\F := by
  intro B L F
  have hLB : L⊆B := markedFiniteResources_mono (Finset.subset_univ _) hSR
  have hIn : ∀ e∈L,markedInnerResource I J e :=
    (markedFiniteResources_support_iff tail head ktail khead π AR SR I J hI).mpr ⟨hA,hS⟩
  have hLI : L⊆B.filter (markedInnerResource I J) :=
    fun e he=>Finset.mem_filter.mpr ⟨hLB he,hIn e he⟩
  refine ⟨hLI,Finset.sdiff_subset,?_⟩
  ext e
  have hh := fun he=>hLI (x:=e) he
  simp only [F,Finset.mem_sdiff] at *
  tauto

end Oberwolfach
