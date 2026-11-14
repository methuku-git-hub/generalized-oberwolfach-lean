module

public import Oberwolfach.MarkedFreeCycle
public import Oberwolfach.FiniteConflictSeparatedChoices

@[expose] public section

/-! Construct a whole family of mutually separated canonical cycles from
one host's fixed intersection bounds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K I:Type} [Fintype V] [Fintype U] [Fintype I]
    [DecidableEq V] [DecidableEq U] [DecidableEq I]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ} {c ch:ℝ}

theorem marked_free_cycle_families
    (Q:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (hl:2≤l) (v₀:V) (W Z:Finset V)
    (hbudget:(W.card:ℝ)+(Fintype.card I*(l+5)+Z.card+l+13)*(2*b+1)<c):
    ∃ C:I→MarkedCycleTuple tail head ktail khead (l+4) π b,
      (∀ i k,(C i).val k∉W∧(C i).val k∉Z∧∀ z∈Z,¬PermutationClose π b ((C i).val k) z)∧
      (∀ i j,i≠j→Disjoint (Finset.univ.image (C i).val) (Finset.univ.image (C j).val))∧
      ∀ i j k k',((i,k):I×Fin (l+5))≠(j,k')→¬PermutationClose π b ((C i).val k) ((C j).val k'):=by
  let S:MarkedCycleTuple tail head ktail khead (l+4) π b→Finset V:=fun C=>Finset.univ.image C.val
  let Good:I→MarkedCycleTuple tail head ktail khead (l+4) π b→Prop:=
    fun _ C=>∀ k,C.val k∉Z∧∀ z∈Z,¬PermutationClose π b (C.val k) z
  have hc:∀ i:I,∀ B:Finset V,(B.card:ℝ)≤W.card+Fintype.card I*(l+5)*((2*b:ℝ)+1)→
      ∃ C,Good i C∧(S C).card≤l+5∧Disjoint (S C) B:=by
    intro i B hB
    have hb:(B.card:ℝ)+(Z.card+l+13)*(2*b+1)<c:=by nlinarith only [hB,hbudget]
    obtain ⟨C,hC⟩:=marked_free_cycle Q hl v₀ B Z hb
    refine ⟨C,fun k=>(hC k).2,?_,?_⟩
    · simpa only [S,Finset.card_univ,Fintype.card_fin] using Finset.card_image_le (s:=Finset.univ) (f:=C.val)
    · apply Finset.disjoint_left.mpr
      intro v hv hB
      obtain ⟨k,_,rfl⟩:=Finset.mem_image.mp hv
      exact (hC k).1 hB
  obtain ⟨C,hC,hd⟩:=finite_conflict_separated_choices S Good W (l+5) (permutationConflictGraph π b) (2*b)
    (by positivity) (fun v=>by exact_mod_cast permutationConflictGraph_degree_le π b v)
    (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hc)
  refine ⟨C,?_,fun i j hij=>(hd i j hij).1,?_⟩
  · intro i k
    exact ⟨fun hh=>Finset.disjoint_left.mp (hC i).2.2 (Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩) hh,(hC i).1 k⟩
  · intro i j k k' hne
    by_cases hij:i=j
    · subst j
      exact (C i).property.1 k k' (fun he=>hne (congrArg (fun k=>(i,k)) he))
    · intro hh
      have hki:((C i).val k)∈S (C i):=Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩
      have hkj:((C j).val k')∈S (C j):=Finset.mem_image.mpr ⟨k',Finset.mem_univ _,rfl⟩
      exact (hd i j hij).2 _ hki _ hkj ⟨fun he=>Finset.disjoint_left.mp (hd i j hij).1 hki (he ▸ hkj),hh⟩

end Oberwolfach
