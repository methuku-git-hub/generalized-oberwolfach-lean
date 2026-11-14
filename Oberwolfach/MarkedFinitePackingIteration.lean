module

public import Oberwolfach.MarkedFiniteResourceOperations
public import Oberwolfach.ResourceDecompositions

@[expose] public section

/-! Finite iteration of actual marked wheel packings in one ambient typed
host. The step invariant is explicit input: this algebraic induction does
not supply the analytic hypotheses for a cover-down step. Divisibility,
edge-disjointness and the exact terminal complement are proved here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K : Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
    [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]
    {tail head : E→V} {ktail khead : K→V} {π : Equiv.Perm V}
    {m b : ℕ} {H₀ HK : V→U→Prop}

theorem markedFiniteResources_mono
    {A B : Finset (E⊕K)} {S T : Finset (V×U)} (hA : A⊆B) (hS : S⊆T) :
    markedFiniteResources tail head ktail khead π A S⊆markedFiniteResources tail head ktail khead π B T :=
  Finset.union_subset_union (Finset.image_subset_image hA) (Finset.image_subset_image hS)

theorem marked_finite_packing_iteration
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hH : ∀ v u,¬(H₀ v u∧HK v u))
    (L : ℕ) (Good : ℕ→Finset (E⊕K)→Finset (V×U)→Prop)
    (hstep : ∀ i<L,∀ A S,Good i A S→MarkedRemainderDivisible tail head ktail khead HK A S m→
      ∃ M : Finset (MarkedWheel tail head ktail khead m π b H₀ HK),
        (∀ W∈M,∀ W'∈M,W≠W'→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources W')) ∧
        M.biUnion markedWheelArcs⊆A ∧ M.biUnion markedWheelSpokePairs⊆S ∧
        Good (i+1) (A\M.biUnion markedWheelArcs) (S\M.biUnion markedWheelSpokePairs))
    (A : Finset (E⊕K)) (S : Finset (V×U)) (hGood : Good 0 A S)
    (hdiv : MarkedRemainderDivisible tail head ktail khead HK A S m) :
    ∃ A'⊆A,∃ S'⊆S,Good L A' S' ∧ MarkedRemainderDivisible tail head ktail khead HK A' S' m ∧
      HasResourceDecomposition
        (fun W : MarkedWheel tail head ktail khead m π b H₀ HK=>markedWheelPhysicalResources W)
        (markedFiniteResources tail head ktail khead π A S\markedFiniteResources tail head ktail khead π A' S') := by
  induction L generalizing Good A S with
  | zero =>
    refine ⟨A,Finset.Subset.refl _,S,Finset.Subset.refl _,hGood,hdiv,?_⟩
    rw [Finset.sdiff_self]
    exact resource_decomposition_empty _
  | succ L ih =>
    obtain ⟨M,hM,hMA,hMS,hMG⟩ := hstep 0 (by omega) A S hGood hdiv
    let A₁ := A\M.biUnion markedWheelArcs
    let S₁ := S\M.biUnion markedWheelSpokePairs
    have hdiv₁ : MarkedRemainderDivisible tail head ktail khead HK A₁ S₁ m :=
      marked_packing_remainder_divisible hH A S hdiv M hM hMA hMS
    obtain ⟨A',hA',S',hS',hGood',hdiv',hdec⟩ := ih (fun i=>Good (i+1))
      (by intro i hi A' S' hg hd;exact hstep (i+1) (by omega) A' S' hg hd) A₁ S₁ hMG hdiv₁
    have hA₁ : A₁⊆A := Finset.sdiff_subset
    have hS₁ : S₁⊆S := Finset.sdiff_subset
    refine ⟨A',hA'.trans hA₁,S',hS'.trans hS₁,hGood',hdiv',?_⟩
    let R := fun W : MarkedWheel tail head ktail khead m π b H₀ HK=>markedWheelPhysicalResources W
    let B₀ := markedFiniteResources tail head ktail khead π A S
    let B₁ := markedFiniteResources tail head ktail khead π A₁ S₁
    let B' := markedFiniteResources tail head ktail khead π A' S'
    have hB₁ : B₁⊆B₀ := markedFiniteResources_mono hA₁ hS₁
    have hB' : B'⊆B₁ := markedFiniteResources_mono hA' hS'
    have hMB : M.biUnion R⊆B₀ := by
      rw [← markedPackingResources_eq_finite]
      exact markedFiniteResources_mono hMA hMS
    have hleft : B₁=B₀\M.biUnion R := by
      dsimp only [B₁,A₁,S₁,B₀]
      rw [markedFiniteResources_sdiff tail head ktail khead π hp,markedPackingResources_eq_finite]
    have hcovered : B₀\B₁=M.biUnion R := by
      rw [hleft]
      ext e
      have hh := fun he=>hMB (x:=e) he
      simp only [Finset.mem_sdiff] at *
      tauto
    have hfirst : HasResourceDecomposition R (B₀\B₁) := by rw [hcovered];exact ⟨M,hM,rfl⟩
    have hdisj : Disjoint (B₀\B₁) (B₁\B') := by
      apply Finset.disjoint_left.mpr
      intro e he he'
      exact (Finset.mem_sdiff.mp he).2 (Finset.mem_sdiff.mp he').1
    have hwhole := resource_decomposition_union R (B₀\B₁) (B₁\B') hfirst hdec hdisj
    have heq : (B₀\B₁)∪(B₁\B')=B₀\B' := by
      ext e
      have hh := fun he=>hB₁ (x:=e) he
      have hh' := fun he=>hB' (x:=e) he
      simp only [Finset.mem_union,Finset.mem_sdiff] at *
      tauto
    rw [heq] at hwhole
    exact hwhole

theorem marked_finite_iteration_with_reserved_absorber
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hH : ∀ v u,¬(H₀ v u∧HK v u))
    (L : ℕ) (Good : ℕ→Finset (E⊕K)→Finset (V×U)→Prop)
    (hstep : ∀ i<L,∀ A S,Good i A S→MarkedRemainderDivisible tail head ktail khead HK A S m→
      ∃ M : Finset (MarkedWheel tail head ktail khead m π b H₀ HK),
        (∀ W∈M,∀ W'∈M,W≠W'→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources W')) ∧
        M.biUnion markedWheelArcs⊆A ∧ M.biUnion markedWheelSpokePairs⊆S ∧
        Good (i+1) (A\M.biUnion markedWheelArcs) (S\M.biUnion markedWheelSpokePairs))
    (A : Finset (E⊕K)) (S : Finset (V×U)) (hGood : Good 0 A S)
    (hdiv : MarkedRemainderDivisible tail head ktail khead HK A S m)
    (C : Finset (Finset V⊕(V×U)))
    (hC : Disjoint C (markedFiniteResources tail head ktail khead π A S))
    (habs : ∀ A'⊆A,∀ S'⊆S,Good L A' S'→MarkedRemainderDivisible tail head ktail khead HK A' S' m→
      HasResourceDecomposition
        (fun W : MarkedWheel tail head ktail khead m π b H₀ HK=>markedWheelPhysicalResources W)
        (C∪markedFiniteResources tail head ktail khead π A' S')) :
    HasResourceDecomposition
      (fun W : MarkedWheel tail head ktail khead m π b H₀ HK=>markedWheelPhysicalResources W)
      (C∪markedFiniteResources tail head ktail khead π A S) := by
  obtain ⟨A',hA',S',hS',hGood',hdiv',hdec⟩ := marked_finite_packing_iteration hp hH L Good hstep A S hGood hdiv
  let B := markedFiniteResources tail head ktail khead π A S
  let B' := markedFiniteResources tail head ktail khead π A' S'
  have hB' : B'⊆B := markedFiniteResources_mono hA' hS'
  have hdisj : Disjoint (B\B') (C∪B') := by
    apply Finset.disjoint_union_right.mpr
    refine ⟨hC.symm.mono_left Finset.sdiff_subset,?_⟩
    exact Finset.disjoint_left.mpr (fun _ h h'=> (Finset.mem_sdiff.mp h).2 h')
  have hwhole := resource_decomposition_union _ (B\B') (C∪B') hdec (habs A' hA' S' hS' hGood' hdiv') hdisj
  have heq : (B\B')∪(C∪B')=C∪B := by
    ext e
    have hh := fun he=>hB' (x:=e) he
    simp only [Finset.mem_union,Finset.mem_sdiff] at *
    tauto
  rw [heq] at hwhole
  exact hwhole

end Oberwolfach
