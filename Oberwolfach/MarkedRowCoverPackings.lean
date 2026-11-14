module

public import Oberwolfach.MarkedRowSupportComparison
public import Oberwolfach.MarkedPackingRimGraphs
public import Oberwolfach.RowCoverPackings

@[expose] public section

/-! Finite marked row covers, with their exact physical resource sets and
local degree bounds. The required set records the supplied root arcs and
spokes; it is not substituted for a host or existence assumption. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E T I : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head : E→V} {ktail khead : T→V} {H₀ HK : V→U→Prop}
    {π : Equiv.Perm V} {m b : ℕ}

def markedPackingSpokes (M : Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (x : V) (u : U) : Prop := ∃ W∈M,W.2.val=u ∧ x∈markedWheelRows W

structure MarkedRowCover (M : Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (v : V) (F : Finset V) (required : Finset (Finset V⊕(V×U))) (allowedHubs : Finset U) (K : ℕ) : Prop where
  disjoint : ∀ W∈M,∀ Z∈M,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z)
  rows : ∀ W∈M,markedWheelRows W⊆insert v F
  hubs : ∀ W∈M,W.2.val∈allowedHubs
  root : ∀ W∈M,v∈markedWheelRows W
  covers : required⊆M.biUnion markedWheelPhysicalResources
  rimDegree : ∀ x,(spanningRestriction (markedPackingRimGraph M) F).degree x≤4*(K+4)
  rowDegree : ∀ x∈F,(Finset.univ.filter (markedPackingSpokes M x)).card≤K+4
  columnDegree : ∀ u,(Finset.univ.filter (fun x=>markedPackingSpokes M x u)).card≤m+1

theorem marked_family_image_rim [Fintype I]
    (C : I→MarkedWheel tail head ktail khead m π b H₀ HK) :
    markedPackingRimGraph (Finset.univ.image C)=markedFamilyRim C := by
  ext x y
  simp only [markedPackingRimGraph,markedPackingRims,physicalEdgeGraph,markedFamilyRim,
    markedWheelRimGraph,SimpleGraph.iSup_adj,Finset.mem_biUnion,Finset.mem_image,Finset.mem_univ,true_and]
  aesop

theorem marked_family_image_spokes [Fintype I]
    (C : I→MarkedWheel tail head ktail khead m π b H₀ HK) :
    markedPackingSpokes (Finset.univ.image C)=markedFamilySpokes C := by
  funext x u
  apply propext
  simp only [markedPackingSpokes,markedFamilySpokes,Finset.mem_image,Finset.mem_univ,true_and]
  aesop

theorem markedPackingSpokes_biUnion {n : ℕ}
    (C : Fin n→Finset (MarkedWheel tail head ktail khead m π b H₀ HK)) (x : V) (u : U) :
    markedPackingSpokes (Finset.univ.biUnion C) x u ↔ ∃ i,markedPackingSpokes (C i) x u := by
  simp only [markedPackingSpokes,Finset.mem_biUnion,Finset.mem_univ,true_and]
  aesop

theorem markedRowCover_of_family [Fintype I]
    (C : I→MarkedWheel tail head ktail khead m π b H₀ HK)
    (v : V) (F : Finset V) (required : Finset (Finset V⊕(V×U))) (allowedHubs : Finset U) (K : ℕ)
    (hC : ∀ i j,i≠j→Disjoint (markedWheelPhysicalResources (C i)) (markedWheelPhysicalResources (C j)))
    (hrows : ∀ i,markedWheelRows (C i)⊆insert v F)
    (hhubs : ∀ i,(C i).2.val∈allowedHubs)
    (hroots : ∀ i,v∈markedWheelRows (C i))
    (hcover : ∀ e∈required,∃ i,e∈markedWheelPhysicalResources (C i))
    (hR : ∀ x,(spanningRestriction (markedFamilyRim C) F).degree x≤4*(K+4))
    (hS : ∀ x∈F,(Finset.univ.filter (markedFamilySpokes C x)).card≤K+4)
    (hCol : ∀ u,(Finset.univ.filter (fun x=>markedFamilySpokes C x u)).card≤m+1) :
    MarkedRowCover (Finset.univ.image C) v F required allowedHubs K := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro W hW Z hZ hne
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hW
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hZ
    exact hC i j (fun he=>hne (congrArg C he))
  · intro W hW
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hW
    exact hrows i
  · intro W hW
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hW
    exact hhubs i
  · intro W hW
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hW
    exact hroots i
  · intro e he
    obtain ⟨i,hi⟩ := hcover e he
    exact Finset.mem_biUnion.mpr ⟨C i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,hi⟩
  · intro x
    have he := congrArg (fun G:SimpleGraph V=>(spanningRestriction G F).degree x) (marked_family_image_rim C)
    exact he.le.trans (by convert hR x using 1 <;> congr!)
  · simpa only [marked_family_image_spokes] using hS
  · simpa only [marked_family_image_spokes] using hCol

end Oberwolfach
