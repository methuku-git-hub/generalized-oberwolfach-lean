module

public import Oberwolfach.BalancedSubsetsPreservingRoots
public import Oberwolfach.HubToRowDeletion

@[expose] public section

/-! The finite class operations in common-neighbourhood balancing. Prescribed
roots survive the successor exclusion and the subsequent exact-ratio trimming. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [DecidableEq V]

 theorem common_class_prebalance (π:Equiv.Perm V) (A₀ B₀ I ZK ZO:Finset V)
    (hZA:ZK⊆A₀) (hZI:Disjoint (ZK∪ZO) I)
    (hsep:Disjoint ZK (ZO.image π.symm)):
    let A:=(A₀\I)\ZO.image π.symm
    let B:=((B₀\I)∪ZO)\A.image π
    ZK⊆A ∧ ZO⊆B ∧ A⊆A₀ ∧ B⊆B₀∪ZO ∧
      Disjoint (A∪B) I ∧ Disjoint B (A.image π) ∧
      ((changed A A₀).card+(changed B B₀).card≤
        (B₀∩A₀.image π).card+2*I.card+2*ZO.card):=by
  intro A B
  have hAA:A⊆A₀:=Finset.sdiff_subset.trans Finset.sdiff_subset
  have hZA':ZK⊆A:=by
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hZA hx,
      fun hi=>Finset.disjoint_left.mp hZI (Finset.mem_union_left _ hx) hi⟩,
      fun hy=>Finset.disjoint_left.mp hsep hx hy⟩
  have hZO':ZO⊆B:=by
    intro x hx
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ hx,?_⟩
    rintro hh
    obtain ⟨y,hy,he⟩:=Finset.mem_image.mp hh
    apply (Finset.mem_sdiff.mp hy).2
    exact Finset.mem_image.mpr ⟨x,hx,by rw [←he];exact π.symm_apply_apply y⟩
  have hBB:B⊆B₀∪ZO:=by
    intro x hx
    rcases (Finset.mem_sdiff.mp hx).1 with hx
    rcases Finset.mem_union.mp hx with hx|hx
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mp hx).1
    · exact Finset.mem_union_right _ hx
  have hAI:Disjoint (A∪B) I:=by
    apply Finset.disjoint_left.mpr
    intro x hx hi
    rcases Finset.mem_union.mp hx with hx|hx
    · exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hx).1).2 hi
    · rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hx).1 with hx|hx
      · exact (Finset.mem_sdiff.mp hx).2 hi
      · exact Finset.disjoint_left.mp hZI (Finset.mem_union_right _ hx) hi
  have hBπ:Disjoint B (A.image π):=by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hx).2 hy
  have hAc:changed A A₀⊆I∪ZO.image π.symm:=by
    intro x hx
    have hh:(x∈A∧x∉A₀)∨(x∈A₀∧x∉A):=by simpa only [changed,Finset.mem_union,Finset.mem_sdiff] using hx
    rcases hh with ⟨hx,hnot⟩|⟨hx,hnot⟩
    · exact False.elim (hnot (hAA hx))
    · by_cases hi:x∈I
      · exact Finset.mem_union_left _ hi
      · apply Finset.mem_union_right
        by_contra hh
        exact hnot (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hx,hi⟩,hh⟩)
  have hBc:changed B B₀⊆(I∪ZO)∪(B₀∩A₀.image π):=by
    intro x hx
    have hh:(x∈B∧x∉B₀)∨(x∈B₀∧x∉B):=by simpa only [changed,Finset.mem_union,Finset.mem_sdiff] using hx
    rcases hh with ⟨hx,hnot⟩|⟨hx,hnot⟩
    · have hzo: x∈ZO:=(Finset.mem_union.mp (hBB hx)).resolve_left hnot
      exact Finset.mem_union_left _ (Finset.mem_union_right _ hzo)
    · by_cases hi:x∈I
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hi)
      · have hh:x∈A.image π:=by
          by_contra hh
          exact hnot (Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx,hi⟩),hh⟩)
        exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hx,Finset.image_subset_image hAA hh⟩)
  have hAc':(changed A A₀).card≤I.card+ZO.card:=by
    have hh:=(Finset.card_le_card hAc).trans (Finset.card_union_le _ _)
    simpa only [Finset.card_image_of_injective _ π.symm.injective] using hh
  have hBc':(changed B B₀).card≤I.card+ZO.card+(B₀∩A₀.image π).card:=by
    exact (Finset.card_le_card hBc).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  exact ⟨hZA',hZO',hAA,hBB,hAI,hBπ,by omega⟩

 theorem changed_card_of_subset (A B:Finset V) (h:A⊆B):
    (changed A B).card=B.card-A.card:=by
  have he:changed A B=B\A:=by
    ext x
    have hx:x∈A→x∈B:=fun hx=>h hx
    simp only [changed,Finset.mem_union,Finset.mem_sdiff]
    tauto
  rw [he,Finset.card_sdiff_of_subset h]

 theorem common_class_balanced_subsets (π:Equiv.Perm V) (A₀ B₀ I ZK ZO:Finset V)
    (s:ℕ) (hs:1≤s) (hZA:ZK⊆A₀) (hZI:Disjoint (ZK∪ZO) I)
    (hsep:Disjoint ZK (ZO.image π.symm)) (hZ:ZO.card=s*ZK.card):
    ∃ A B:Finset V,ZK⊆A∧ZO⊆B∧A⊆A₀∧B⊆B₀∪ZO∧
      Disjoint (A∪B) I∧Disjoint B (A.image π)∧B.card=s*A.card∧
      (((changed A A₀).card:ℝ)+(changed B B₀).card≤
        |(B₀.card:ℝ)-s*A₀.card|+(s+1)*((B₀∩A₀.image π).card+2*I.card+2*ZO.card)+s-1):=by
  let A₁:=(A₀\I)\ZO.image π.symm
  let B₁:=((B₀\I)∪ZO)\A₁.image π
  have hp:=common_class_prebalance π A₀ B₀ I ZK ZO hZA hZI hsep
  obtain ⟨A,B,hZK,hA,hZO,hB,hcard,_,hloss⟩:=balanced_subsets_preserving_roots A₁ B₁ ZK ZO s hs hp.1 hp.2.1 hZ
  have hAI:Disjoint (A∪B) I:=hp.2.2.2.2.1.mono_left (Finset.union_subset_union hA hB)
  have hBπ:Disjoint B (A.image π):=hp.2.2.2.2.2.1.mono hB (Finset.image_subset_image hA)
  refine ⟨A,B,hZK,hZO,hA.trans hp.2.2.1,hB.trans hp.2.2.2.1,hAI,hBπ,hcard,?_⟩
  have hbound:((changed A₁ A₀).card:ℝ)+(changed B₁ B₀).card≤
      (B₀∩A₀.image π).card+2*I.card+2*ZO.card:=by exact_mod_cast hp.2.2.2.2.2.2
  have hda:=card_difference_le_changed A₁ A₀
  have hdb:=card_difference_le_changed B₁ B₀
  have hsR:(1:ℝ)≤s:=by exact_mod_cast hs
  have himb:|(B₁.card:ℝ)-s*A₁.card|≤|(B₀.card:ℝ)-s*A₀.card|+
      (changed B₁ B₀).card+s*(changed A₁ A₀).card:=by
    calc
      _ = |((B₁.card:ℝ)-B₀.card)+((B₀.card:ℝ)-s*A₀.card)-s*((A₁.card:ℝ)-A₀.card)|:=by congr 1;ring
      _ ≤ |(B₁.card:ℝ)-B₀.card|+|(B₀.card:ℝ)-s*A₀.card|+|s*((A₁.card:ℝ)-A₀.card)|:=by
        exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ _:=by rw [abs_mul,abs_of_nonneg (show (0:ℝ)≤s by positivity)];nlinarith only [hda,hdb,hsR]
  have hca:((changed A A₀).card:ℝ)≤(A₁.card:ℝ)-A.card+(changed A₁ A₀).card:=by
    have hh:=changed_card_triangle A A₁ A₀
    rw [changed_card_of_subset A A₁ hA] at hh
    have hhR:((changed A A₀).card:ℝ)≤(A₁.card-A.card:ℕ)+(changed A₁ A₀).card:=by exact_mod_cast hh
    rw [Nat.cast_sub (Finset.card_le_card hA)] at hhR
    exact hhR
  have hcb:((changed B B₀).card:ℝ)≤(B₁.card:ℝ)-B.card+(changed B₁ B₀).card:=by
    have hh:=changed_card_triangle B B₁ B₀
    rw [changed_card_of_subset B B₁ hB] at hh
    have hhR:((changed B B₀).card:ℝ)≤(B₁.card-B.card:ℕ)+(changed B₁ B₀).card:=by exact_mod_cast hh
    rw [Nat.cast_sub (Finset.card_le_card hB)] at hhR
    exact hhR
  have hnonneg:(0:ℝ)≤(changed B₁ B₀).card:=by positivity
  nlinarith only [hca,hcb,hloss,himb,hbound,hsR,hnonneg]

end Oberwolfach
