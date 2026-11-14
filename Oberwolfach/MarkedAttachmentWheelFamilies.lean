module

public import Oberwolfach.MarkedRimAttachedWheel
public import Oberwolfach.MarkedAttachedCycle
public import Oberwolfach.FiniteSeparatedRowHubChoices

@[expose] public section

/-! Simultaneous wheels attached at the prescribed old rows. Only their
other vertices are new; repeated or close old rows are allowed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K A S:Type} [Fintype V] [Fintype U] [Fintype A] [Fintype S]
    [DecidableEq V] [DecidableEq U] [DecidableEq A] [DecidableEq S]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ} {c ch:ℝ}

def markedAttachmentPosition (l:ℕ) (jr:A→Bool) (js:S→Bool):(A⊕S)→Fin (l+5):=
  Sum.elim (fun a=>markedExpansionRimPosition (l+4) (by omega) (jr a))
    (fun s=>markedExpansionSpokePosition (l+4) (by omega) (js s))

theorem marked_attachment_wheel_families
    (Q:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (hl:2≤l) (src:A→V) (row:S→V) (jr:A→Bool) (js:S→Bool)
    (W Z:Finset V) (B:Finset U) (hr:∀ a,src a∈Z) (hs:∀ s,row s∈Z)
    (hbudget:(W.card:ℝ)+(Z.card+Fintype.card (A⊕S)*(l+5)+l+12)*(2*b+1)<c)
    (hB:(B.card:ℝ)+Fintype.card (A⊕S)<ch):
    let k:=markedAttachmentPosition l jr js
    ∃ C:(A⊕S)→MarkedWheel tail head ktail khead (l+4) π b H₀ HK,
      (∀ i,(C i).1.val (k i)=Sum.elim src row i)∧
      (∀ i,(C i).2.val∉B)∧Function.Injective (fun i=>(C i).2.val)∧
      (∀ i t,t≠k i→(C i).1.val t∉W∧(C i).1.val t∉Z∧∀ z∈Z,¬PermutationClose π b ((C i).1.val t) z)∧
      (∀ i j,i≠j→Disjoint ((Finset.univ.filter (·≠k i)).image (C i).1.val)
        ((Finset.univ.filter (·≠k j)).image (C j).1.val))∧
      ∀ i j t t',t≠k i→t'≠k j→((i,t):(A⊕S)×Fin (l+5))≠(j,t')→
        ¬PermutationClose π b ((C i).1.val t) ((C j).1.val t'):=by
  dsimp only
  let k:=markedAttachmentPosition l jr js
  let rows:(A⊕S)→MarkedWheel tail head ktail khead (l+4) π b H₀ HK→Finset V:=
    fun i C=>(Finset.univ.filter (·≠k i)).image C.1.val
  let hubs:(A⊕S)→MarkedWheel tail head ktail khead (l+4) π b H₀ HK→Finset U:=fun _ C=>{C.2.val}
  let Good:(A⊕S)→MarkedWheel tail head ktail khead (l+4) π b H₀ HK→Prop:=
    fun i C=>C.1.val (k i)=Sum.elim src row i∧∀ t,t≠k i→C.1.val t∉W
  have hchoose:∀ Z':Finset V,∀ B':Finset U,Z⊆Z'→B⊆B'→
      Z'.card≤Z.card+Fintype.card (A⊕S)*(l+5)→B'.card≤B.card+Fintype.card (A⊕S)*1→∀ i:A⊕S,
      ∃ C,Good i C∧(rows i C).card≤l+5∧(hubs i C).card≤1∧Disjoint (rows i C) Z'∧Disjoint (hubs i C) B'∧
        ∀ v∈rows i C,∀ w∈Z',¬PermutationClose π b v w:=by
    intro Z' B' hZZ hBB hZc hBc i
    have hbrow:(W.card:ℝ)+(Z'.card+l+12)*(2*b+1)<c:=by
      have hz:(Z'.card:ℝ)≤Z.card+Fintype.card (A⊕S)*(l+5):=by exact_mod_cast hZc
      have hh:=mul_le_mul_of_nonneg_right (show (Z'.card:ℝ)+l+12≤Z.card+Fintype.card (A⊕S)*(l+5)+l+12 by linarith only [hz])
        (show 0≤(2*b+1:ℝ) by positivity)
      linarith only [hh,hbudget]
    have hbhub:(B'.card:ℝ)<ch:=by
      have hb:(B'.card:ℝ)≤B.card+Fintype.card (A⊕S):=by exact_mod_cast (by simpa using hBc)
      exact hb.trans_lt hB
    have hex:∃ C:MarkedWheel tail head ktail khead (l+4) π b H₀ HK,
        C.1.val (k i)=Sum.elim src row i∧C.2.val∉B'∧
        ∀ t,t≠k i→C.1.val t∉W∧C.1.val t∉Z'∧∀ z∈Z',¬PermutationClose π b (C.1.val t) z:=by
      cases i with
      | inl a=>exact marked_wheel_at_rim_position_fresh_hub Q hl (jr a) W Z' B' (src a) (hZZ (hr a)) hbrow hbhub
      | inr s=>exact marked_wheel_at_typed_position_fresh_hub Q hl (js s) W Z' B' (row s) (hZZ (hs s)) hbrow hbhub
    obtain ⟨C,hC,hCB,hav⟩:=hex
    refine ⟨C,⟨hC,fun t ht=>(hav t ht).1⟩,?_,by simp [hubs],?_,by simpa only [hubs,Finset.disjoint_singleton_left] using hCB,?_⟩
    · exact (Finset.card_image_le).trans ((Finset.card_filter_le _ _).trans (by simp))
    · apply Finset.disjoint_left.mpr
      intro v hv hz
      obtain ⟨t,ht,rfl⟩:=Finset.mem_image.mp hv
      exact (hav t (Finset.mem_filter.mp ht).2).2.1 hz
    · intro v hv z hz
      obtain ⟨t,ht,rfl⟩:=Finset.mem_image.mp hv
      exact (hav t (Finset.mem_filter.mp ht).2).2.2 z hz
  obtain ⟨C,hC,hd⟩:=finite_separated_row_hub_choices π b rows hubs Good Z B (l+5) 1 hchoose
  have hmem (i:A⊕S) (t:Fin (l+5)) (ht:t≠k i):(C i).1.val t∈rows i (C i):=
    Finset.mem_image.mpr ⟨t,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩,rfl⟩
  refine ⟨C,fun i=>(hC i).1.1,?_,?_,?_,fun i j hij=>(hd i j hij).1,?_⟩
  · intro i;exact Finset.disjoint_left.mp (hC i).2.2.2.2.1 (Finset.mem_singleton_self _)
  · intro i j he;by_contra hij
    exact Finset.disjoint_left.mp (hd i j hij).2.1 (Finset.mem_singleton_self _) (by simp [hubs,he])
  · intro i t ht
    exact ⟨(hC i).1.2 t ht,Finset.disjoint_left.mp (hC i).2.2.2.1 (hmem i t ht),
      (hC i).2.2.2.2.2 _ (hmem i t ht)⟩
  · intro i j t t' ht ht' hne
    by_cases hij:i=j
    · subst j;exact (C i).1.property.1 t t' (fun he=>hne (congrArg (fun t=>(i,t)) he))
    · exact (hd i j hij).2.2 _ (hmem i t ht) _ (hmem j t' ht')

end Oberwolfach
