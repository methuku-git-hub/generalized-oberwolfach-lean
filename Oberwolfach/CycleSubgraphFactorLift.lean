module

public import Oberwolfach.OrdinaryFactorGraphs

@[expose] public section
/-! The inclusion of a spanning subgraph preserves cycle supports,
packing, coverage, and physical edge sets. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

def ordinaryCycleSubgraphLift {G Q:SimpleGraph V} {r:ℕ} (hQ:Q≤G)
    (C:OrdinaryCycle Q r):OrdinaryCycle G r:=⟨C.val,C.property.trans hQ⟩

theorem ordinary_subgraph_factor_lift {G Q:SimpleGraph V} {r:ℕ} (hQ:Q≤G)
    (A:Finset V) (M:Finset (OrdinaryCycle Q r))
    (hpack:∀ C∈M,∀ E∈M,C≠E→Disjoint (ordinaryCycleVertices Q r C) (ordinaryCycleVertices Q r E))
    (hcover:M.biUnion (ordinaryCycleVertices Q r)=A):
    let lift:=ordinaryCycleSubgraphLift hQ;
    (∀ C∈M.image lift,∀ E∈M.image lift,C≠E→Disjoint (ordinaryCycleVertices G r C) (ordinaryCycleVertices G r E)) ∧
    (M.image lift).biUnion (ordinaryCycleVertices G r)=A:=by
  intro lift
  constructor
  · intro C hC E hE hne
    obtain ⟨C',hC',hCC⟩:=Finset.mem_image.mp hC
    obtain ⟨E',hE',hEE⟩:=Finset.mem_image.mp hE
    subst C;subst E
    exact hpack C' hC' E' hE' (fun he=>hne (congrArg lift he))
  · rw [←hcover]
    ext v
    simp only [Finset.mem_biUnion,Finset.mem_image]
    constructor
    · rintro ⟨_,⟨C,hC,rfl⟩,hv⟩;exact ⟨C,hC,hv⟩
    · rintro ⟨C,hC,hv⟩;exact ⟨lift C,⟨C,hC,rfl⟩,hv⟩
end Oberwolfach
