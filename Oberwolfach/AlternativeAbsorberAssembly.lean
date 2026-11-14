module

public import Oberwolfach.UniversalAbsorberReservoir

@[expose] public section

/-! A fixed union absorbs each member of a finite family of alternative
remainders. The alternatives may overlap; only their absorber resources
must be disjoint, and avoid every alternative. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem alternative_absorber_union {I E W:Type*} [Fintype I] [DecidableEq I]
    [DecidableEq E] [DecidableEq W]
    (R:W→Finset E) (X A:I→Finset E)
    (hA:∀ i,IsResourceAbsorber R (X i) (A i))
    (hAA:∀ i j,i≠j→Disjoint (A i) (A j))
    (hAX:∀ i j,Disjoint (A i) (X j)):
    HasResourceDecomposition R (Finset.univ.biUnion A)∧
      ∀ i,IsResourceAbsorber R (X i) (Finset.univ.biUnion A) := by
  refine ⟨resource_decomposition_biUnion R A Finset.univ (fun i _=>(hA i).2.1)
    (fun i _ j _=>hAA i j),?_⟩
  have hchoices (i:I):(1:ℝ)≤((Finset.univ.filter (fun j=>HasResourceDecomposition R (A j∪X i))).card:ℝ):=by
    exact_mod_cast (Finset.one_le_card.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hA i).2.2⟩⟩)
  have hu:=universal_absorber_reservoir R X A Finset.univ 1
    (fun i _ j _=>hAA i j) (fun i _=>(hA i).2.1) hchoices
  intro i
  have hd:Disjoint (({i}:Finset I).biUnion X) (Finset.univ.biUnion A):=by
    simp only [Finset.singleton_biUnion]
    apply Finset.disjoint_left.mpr
    intro e he hx
    obtain ⟨j,_,hj⟩:=Finset.mem_biUnion.mp hx
    exact Finset.disjoint_left.mp (hAX j i) hj he
  have hh:=hu {i} (by simp) (by intro j hj k hk hne;simp only [Finset.mem_singleton] at hj hk;exact (hne (hj.trans hk.symm)).elim) hd
  simpa only [Finset.singleton_biUnion] using hh

end Oberwolfach
