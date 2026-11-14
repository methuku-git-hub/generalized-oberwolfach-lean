module

public import Oberwolfach.RootPackingDivisibility
public import Oberwolfach.OrdinaryFactorGraphs

@[expose] public section
/-! A factor on the fresh vertices not used by the rooted cycles completes
the packing, without putting two roots on one cycle. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem extend_rooted_cycle_packing {V:Type} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) (r:ℕ) (S T:Finset V)
    (M₀ M:Finset (OrdinaryCycle G r))
    (hpart:S∪T=Finset.univ) (hdis:Disjoint S T)
    (hpack₀:∀ C∈M₀,∀ E∈M₀,C≠E→Disjoint (ordinaryCycleVertices G r C) (ordinaryCycleVertices G r E))
    (hcover₀:T⊆M₀.biUnion (ordinaryCycleVertices G r))
    (hroot:∀ C∈M₀,∃ x∈T,x∈ordinaryCycleVertices G r C ∧ ∀ y∈T,y∈ordinaryCycleVertices G r C→y=x)
    (hpack:∀ C∈M,∀ E∈M,C≠E→Disjoint (ordinaryCycleVertices G r C) (ordinaryCycleVertices G r E))
    (hcover:M.biUnion (ordinaryCycleVertices G r)=S\M₀.biUnion (ordinaryCycleVertices G r)):
    let M₁:=M₀∪M;
    (∀ C∈M₁,∀ E∈M₁,C≠E→Disjoint (ordinaryCycleVertices G r C) (ordinaryCycleVertices G r E)) ∧
    M₁.biUnion (ordinaryCycleVertices G r)=Finset.univ ∧
    (∀ C∈M₁,(ordinaryCycleVertices G r C∩T).card≤1) :=by
  intro M₁
  let U:=M₀.biUnion (ordinaryCycleVertices G r)
  have hres (C:OrdinaryCycle G r) (hC:C∈M):ordinaryCycleVertices G r C⊆S\U:=by
    intro v hv
    rw [←hcover]
    exact Finset.mem_biUnion.mpr ⟨C,hC,hv⟩
  have hrootdis (C:OrdinaryCycle G r) (hC:C∈M₀) (E:OrdinaryCycle G r) (hE:E∈M):
      Disjoint (ordinaryCycleVertices G r C) (ordinaryCycleVertices G r E):=by
    apply Finset.disjoint_left.mpr
    intro v hvC hvE
    have hvU:v∈U:=Finset.mem_biUnion.mpr ⟨C,hC,hvC⟩
    exact (Finset.mem_sdiff.mp (hres E hE hvE)).2 hvU
  refine ⟨?_,?_,?_⟩
  · intro C hC E hE hne
    rcases Finset.mem_union.mp hC with hC|hC <;> rcases Finset.mem_union.mp hE with hE|hE
    · exact hpack₀ C hC E hE hne
    · exact hrootdis C hC E hE
    · exact (hrootdis E hE C hC).symm
    · exact hpack C hC E hE hne
  · ext v
    constructor
    · intro _;exact Finset.mem_univ _
    · intro _
      have hv:v∈S∨v∈T:=by
        have hv':v∈S∪T:=by rw [hpart];exact Finset.mem_univ _
        exact Finset.mem_union.mp hv'
      rcases hv with hvS|hvT
      · by_cases hvU:v∈U
        · obtain ⟨C,hC,hvC⟩:=Finset.mem_biUnion.mp hvU
          exact Finset.mem_biUnion.mpr ⟨C,Finset.mem_union_left _ hC,hvC⟩
        · have hvA:v∈S\U:=Finset.mem_sdiff.mpr ⟨hvS,hvU⟩
          rw [←hcover] at hvA
          obtain ⟨C,hC,hvC⟩:=Finset.mem_biUnion.mp hvA
          exact Finset.mem_biUnion.mpr ⟨C,Finset.mem_union_right _ hC,hvC⟩
      · obtain ⟨C,hC,hvC⟩:=Finset.mem_biUnion.mp (hcover₀ hvT)
        exact Finset.mem_biUnion.mpr ⟨C,Finset.mem_union_left _ hC,hvC⟩
  · intro C hC
    rcases Finset.mem_union.mp hC with hC|hC
    · obtain ⟨x,hxT,hxC,hunique⟩:=hroot C hC
      apply Finset.card_le_one.mpr
      intro y hy z hz
      have hy':=Finset.mem_inter.mp hy
      have hz':=Finset.mem_inter.mp hz
      exact (hunique y hy'.2 hy'.1).trans (hunique z hz'.2 hz'.1).symm
    · have hzero:ordinaryCycleVertices G r C∩T=∅:=by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro v hv
        have hv':=Finset.mem_inter.mp hv
        exact (Finset.disjoint_left.mp hdis) (Finset.mem_sdiff.mp (hres C hC hv'.1)).1 hv'.2
      simp [hzero]
end Oberwolfach
