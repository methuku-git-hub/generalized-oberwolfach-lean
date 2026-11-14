module

public import Oberwolfach.MarkedRimExpansionWheel
public import Oberwolfach.MarkedSpokeExpansionWheel
public import Oberwolfach.FiniteSeparatedRowHubChoices

@[expose] public section

/-! Construct all private wheels and crossed incidences of an expansion in
one host, retaining row separation and distinct new hubs across both rim
and spoke occurrences. Formal old arcs and spokes need not exist. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K A S:Type} [Fintype V] [Fintype U] [Fintype A] [Fintype S]
    [DecidableEq V] [DecidableEq U] [DecidableEq A] [DecidableEq S]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ} {c ch:ℝ}

def MarkedExpansionWheelConditions (src dst:A→V) (row:S→V) (hub:S→U) (jr:A→Bool) (js:S→Bool)
    (i:A⊕S) (C:MarkedWheel tail head ktail khead (l+4) π b H₀ HK):Prop:=
  match i with
  | .inl a=>markedArcPresent tail head ktail khead (jr a) (src a)
      (C.1.val (finRotate (l+5) (markedExpansionRimPosition (l+4) (by omega) (jr a))))∧
      markedArcPresent tail head ktail khead (jr a)
      (C.1.val (markedExpansionRimPosition (l+4) (by omega) (jr a))) (dst a)
  | .inr s=>(if js s then HK (row s) C.2.val else H₀ (row s) C.2.val)∧
      (if js s then HK (C.1.val (markedExpansionSpokePosition (l+4) (by omega) (js s))) (hub s)
        else H₀ (C.1.val (markedExpansionSpokePosition (l+4) (by omega) (js s))) (hub s))

theorem marked_expansion_wheel_families
    (Q:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (hl:2≤l) (src dst:A→V) (row:S→V) (hub:S→U) (jr:A→Bool) (js:S→Bool)
    (W Z:Finset V) (B:Finset U) (hr:∀ a,src a∈Z∧dst a∈Z) (hs:∀ s,row s∈Z)
    (hbudget:(W.card:ℝ)+(Z.card+Fintype.card (A⊕S)*(l+5)+l+16)*(2*b+1)<c)
    (hB:(B.card:ℝ)+Fintype.card (A⊕S)<ch):
    ∃ C:(A⊕S)→MarkedWheel tail head ktail khead (l+4) π b H₀ HK,
      (∀ i,MarkedExpansionWheelConditions src dst row hub jr js i (C i))∧
      (∀ i,(C i).2.val∉B)∧Function.Injective (fun i=>(C i).2.val)∧
      (∀ i k,(C i).1.val k∉W∧(C i).1.val k∉Z∧∀ z∈Z,¬PermutationClose π b ((C i).1.val k) z)∧
      (∀ i j,i≠j→Disjoint (Finset.univ.image (C i).1.val) (Finset.univ.image (C j).1.val))∧
      ∀ i j k k',((i,k):(A⊕S)×Fin (l+5))≠(j,k')→¬PermutationClose π b ((C i).1.val k) ((C j).1.val k'):=by
  let rows:(A⊕S)→MarkedWheel tail head ktail khead (l+4) π b H₀ HK→Finset V:=fun _ C=>Finset.univ.image C.1.val
  let hubs:(A⊕S)→MarkedWheel tail head ktail khead (l+4) π b H₀ HK→Finset U:=fun _ C=>{C.2.val}
  let Good:(A⊕S)→MarkedWheel tail head ktail khead (l+4) π b H₀ HK→Prop:=fun i C=>MarkedExpansionWheelConditions src dst row hub jr js i C∧∀ k,C.1.val k∉W
  have hchoose:∀ Z':Finset V,∀ B':Finset U,Z⊆Z'→B⊆B'→
      Z'.card≤Z.card+Fintype.card (A⊕S)*(l+5)→B'.card≤B.card+Fintype.card (A⊕S)*1→∀ i:A⊕S,
      ∃ C,Good i C∧(rows i C).card≤l+5∧(hubs i C).card≤1∧Disjoint (rows i C) Z'∧Disjoint (hubs i C) B'∧
        ∀ v∈rows i C,∀ w∈Z',¬PermutationClose π b v w:=by
    intro Z' B' hZZ hBB hZc hBc i
    have hbrow:(W.card:ℝ)+(Z'.card+l+16)*(2*b+1)<c:=by
      have hz:(Z'.card:ℝ)≤Z.card+Fintype.card (A⊕S)*(l+5):=by exact_mod_cast hZc
      have hh:=mul_le_mul_of_nonneg_right (show (Z'.card:ℝ)+l+16≤Z.card+Fintype.card (A⊕S)*(l+5)+l+16 by linarith only [hz])
        (show 0≤(2*b+1:ℝ) by positivity)
      linarith only [hh,hbudget]
    have hbhub:(B'.card:ℝ)<ch:=by
      have hb:(B'.card:ℝ)≤B.card+Fintype.card (A⊕S):=by exact_mod_cast (by simpa using hBc)
      exact hb.trans_lt hB
    have hex:∃ C:MarkedWheel tail head ktail khead (l+4) π b H₀ HK,
        MarkedExpansionWheelConditions src dst row hub jr js i C∧C.2.val∉B'∧
        ∀ k,C.1.val k∉W∧C.1.val k∉Z'∧∀ z∈Z',¬PermutationClose π b (C.1.val k) z:=by
      cases i with
      | inl a=>
        obtain ⟨C,hC,hx,hy,hav⟩:=marked_rim_expansion_wheel Q hl (jr a) W Z' B' (src a) (dst a)
          (hZZ (hr a).1) (hZZ (hr a).2) hbrow hbhub
        exact ⟨C,⟨hx,hy⟩,hC,hav⟩
      | inr s=>
        obtain ⟨C,hC,hx,hy,hav⟩:=marked_spoke_expansion_wheel Q hl (js s) W Z' B' (row s) (hub s)
          (hZZ (hs s)) hbrow hbhub
        exact ⟨C,⟨hx,hy⟩,hC,hav⟩
    obtain ⟨C,hC,hCB,hav⟩:=hex
    refine ⟨C,⟨hC,fun k=>(hav k).1⟩,?_,by simp [hubs],?_,by simpa only [hubs,Finset.disjoint_singleton_left] using hCB,?_⟩
    · simpa only [rows,Finset.card_univ,Fintype.card_fin] using Finset.card_image_le (s:=Finset.univ) (f:=C.1.val)
    · apply Finset.disjoint_left.mpr
      intro v hv hz
      obtain ⟨k,_,rfl⟩:=Finset.mem_image.mp hv
      exact (hav k).2.1 hz
    · intro v hv z hz
      obtain ⟨k,_,rfl⟩:=Finset.mem_image.mp hv
      exact (hav k).2.2 z hz
  obtain ⟨C,hC,hd⟩:=finite_separated_row_hub_choices π b rows hubs Good Z B (l+5) 1 hchoose
  refine ⟨C,fun i=>(hC i).1.1,?_,?_,?_,fun i j hij=>(hd i j hij).1,?_⟩
  · intro i;exact Finset.disjoint_left.mp (hC i).2.2.2.2.1 (Finset.mem_singleton_self _)
  · intro i j he;by_contra hij
    exact Finset.disjoint_left.mp (hd i j hij).2.1 (Finset.mem_singleton_self _) (by simp [hubs,he])
  · intro i k
    have hk:(C i).1.val k∈rows i (C i):=Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩
    exact ⟨(hC i).1.2 k,Finset.disjoint_left.mp (hC i).2.2.2.1 hk,(hC i).2.2.2.2.2 _ hk⟩
  · intro i j k k' hne
    by_cases hij:i=j
    · subst j;exact (C i).1.property.1 k k' (fun he=>hne (congrArg (fun k=>(i,k)) he))
    · exact (hd i j hij).2.2 _ (Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩)
        _ (Finset.mem_image.mpr ⟨k',Finset.mem_univ _,rfl⟩)

end Oberwolfach
