module

public import Oberwolfach.EndpointPathTriangles
public import Oberwolfach.PairedAbsorberCounts
public import Oberwolfach.OrdinaryLocalAbsorbers

@[expose] public section

/-! Actual paired absorbers for endpoint triangles. The base triangle avoids
all prescribed row conflicts, so each later row-root pair is nonconflicting.
There is no assumption that the two prescribed row roots avoid each other. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 256
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem endpoint_paired_absorber_count (Q F : SimpleGraph V) (S T : Finset V)
    (hST : Disjoint S T) (γ L : ℝ) (hγ : 0<γ) (hL : 0≤L)
    (hF : ∀ v,(F.degree v:ℝ)≤L)
    (hcommon : EndpointNeighbourCounts Q F S T (γ*Fintype.card V))
    (hbudget : 6*(L+1)≤γ/2*Fintype.card V)
    (hnb : 18≤ordinaryLocalCountCoeff 2 γ*Fintype.card V)
    (hnp : 48≤ordinaryLocalCountCoeff 2 γ*Fintype.card V)
    (x : Fin 3→V) (hx : Function.Injective x)
    (hxclass : ∀ i,x i∈endpointBaseClass S T i.val) :
    (ordinaryLocalCountCoeff 2 γ/2)^4*(Fintype.card V:ℝ)^9≤
      Fintype.card (LabelledCycleRecord (endpointTriangleVertices (Q:=Q) (F:=F) (S:=S) (T:=T))
        (pairedAbsorberTemplate 3).val (Finset.univ.image x)) := by
  let n : ℝ := Fintype.card V
  let a := γ/2*n
  let β := ordinaryLocalCountCoeff 2 γ
  let W := Finset.univ.image x
  have hW : W.card=3 := by rw [Finset.card_image_of_injective _ hx];simp
  let Base := fun f : Fin 3→V=>ClassSparseGreedyGood Q F (endpointBaseClass S T) W allPreviousLabels f
  let Path := fun y : Fin 3→V=>fun i : ℕ=>fun f : Fin 2→V=>
    ∃ hi : i<3,ClassSparseGreedyGood Q F (endpointPathClass S T (decide (i=0))) {x ⟨i,hi⟩,y ⟨i,hi⟩}
      (endpointPathRequirements (x ⟨i,hi⟩) (y ⟨i,hi⟩)) f
  have ha : 0≤a := by dsimp [a,n];positivity
  have hbase0 := endpoint_base_count Q F S T W hST L (γ*n) a hL ha hF hcommon (by
    rw [hW];dsimp [a];norm_num;linarith only [hbudget])
  have hbase : β*n^3≤Fintype.card {f // Base f} := by
    have hh := mul_le_mul_of_nonneg_right (min_le_left ((γ/2)^3) ((γ/2)^2))
      (pow_nonneg (show 0≤n by dsimp [n];positivity) 3)
    have he : a^3=(γ/2)^3*n^3 := mul_pow _ _ _
    exact hh.trans (he ▸ hbase0)
  have hpath (y : Fin 3→V) (hy : Base y) (i : ℕ) (hi : i<3) :
      β*n^2≤Fintype.card {f // Path y i f} := by
    let j : Fin 3 := ⟨i,hi⟩
    have hxy : x j≠y j := fun h=>(hy.2.1 j).2 (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,h⟩)
    have hFxy : ¬F.Adj (x j) (y j) := fun h=>hy.2.2.2.1 j (x j)
      (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩) h.symm
    have hxj : x j∈if decide (i=0) then T else S := by simpa [endpointBaseClass,j] using hxclass j
    have hyj : y j∈if decide (i=0) then T else S := by simpa [endpointBaseClass,j] using (hy.2.1 j).1
    have hh := endpoint_path_count Q F S T L (γ*n) a hL ha hF hcommon
      (by dsimp [a];nlinarith only [hbudget,hL]) (decide (i=0)) (x j) (y j) hxy hFxy hxj hyj
    have hβ := mul_le_mul_of_nonneg_right (min_le_right ((γ/2)^3) ((γ/2)^2))
      (pow_nonneg (show 0≤n by dsimp [n];positivity) 2)
    have he : a^2=(γ/2)^2*n^2 := mul_pow _ _ _
    have hc := hβ.trans (he ▸ hh)
    have hiff (f : Fin 2→V) : Path y i f ↔ ClassSparseGreedyGood Q F
        (endpointPathClass S T (decide (i=0))) {x j,y j} (endpointPathRequirements (x j) (y j)) f := by
      constructor
      · rintro ⟨hi',hf⟩;exact hf
      · intro hf;exact ⟨hi,hf⟩
    exact hc.trans_eq (by exact_mod_cast (Fintype.card_congr (Equiv.subtypeEquivRight hiff)).symm)
  apply paired_absorber_abundance (endpointTriangleVertices (Q:=Q) (F:=F) (S:=S) (T:=T)) (m:=2) (by norm_num)
    x hx Base Path β (ordinaryLocalCountCoeff_pos 2 γ hγ)
    (fun y hy=>hy.1) (fun y hy=>endpoint_base_tuple Q F S T W hST y hy)
    (fun y hy _ i f hf=>?_) (fun y _ _ i _ f hf=>?_) hbase
    (fun y hy _ i hi=>by convert hpath y hy i hi using 1 <;> congr!) (by norm_num at *;exact hnb) (by norm_num at *;exact hnp)
  · obtain ⟨hi,hf⟩ := hf
    have hxj : x i∈if decide (i.val=0) then T else S := by simpa [endpointBaseClass] using hxclass i
    have hyj : y i∈if decide (i.val=0) then T else S := by simpa [endpointBaseClass] using (hy.2.1 i).1
    exact ⟨endpoint_path_triangle Q F S T hST _ (x i) (y i) (y i) (by simp) hyj f hf,
      endpoint_path_triangle Q F S T hST _ (x i) (y i) (x i) (by simp) hxj f hf⟩
  · obtain ⟨hi,hf⟩ := hf
    exact hf.1

end Oberwolfach
