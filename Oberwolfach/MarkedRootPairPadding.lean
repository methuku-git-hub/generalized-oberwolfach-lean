module

public import Oberwolfach.MarkedRootPair
public import Oberwolfach.MarkedPairedPaddingRootGeometry
public import Oberwolfach.MarkedPaddingResourcePair

@[expose] public section

/-! Construct the augmented pair from actual paired padding wheels.
Every typed, degree, map and physical-injectivity field is derived here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 40000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K A S I:Type} [Fintype V] [Fintype U] [Fintype A] [Fintype S] [Fintype I]
    [DecidableEq V] [DecidableEq U] [DecidableEq I]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b m:ℕ}

def MarkedRootPair.pad (G:MarkedRootPair tail head ktail khead H₀ HK π b m A S)
    (hm:0<m) (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (v:I→V) (p:Bool×I→(Fin m↪V)) (h:(Bool×I)↪U)
    (C:Bool×I→MarkedWheel tail head ktail khead m π b H₀ HK) (φ':V→V) (ψ':U→U)
    (hv:∀ i,v i∈G.R∧G.φ (v i)∈G.R')
    (hpair:∀ i,¬PermutationClose π b (v i) (G.φ (v i)))
    (hφ:∀ z∈G.R∪G.R',φ' z=G.φ z) (hψ:∀ z∈G.B,ψ' z=G.ψ z)
    (hmap:∀ i k,φ' ((C (false,i)).1.val k)=(C (true,i)).1.val k)
    (hhmap:∀ i,ψ' (h (false,i))=h (true,i))
    (hh:∀ i,(C i).2.val=h i∧h i∉G.B)
    (hC:∀ i k,(C i).1.val k=Fin.cons (α:=fun _=>V) (if i.1 then G.φ (v i.2) else v i.2) (p i) k)
    (hav:∀ i k,p i k∉G.R∪G.R'∧∀ z∈G.R∪G.R',¬PermutationClose π b (p i k) z)
    (hdis:∀ i j,i≠j→Disjoint (Finset.univ.image (p i)) (Finset.univ.image (p j)))
    (hsep:∀ i j,∀ k k',p i k≠p j k'→¬PermutationClose π b (p i k) (p j k'))
    (hpack:∀ i j,i≠j→Disjoint (markedWheelPhysicalResources (C i)) (markedWheelPhysicalResources (C j))):
    MarkedRootPair tail head ktail khead H₀ HK π b m (A⊕(I×Fin (m+1))) (S⊕(I×Fin (m+1))):=by
  let C₀:=fun i=>(C (false,i)).1.val
  let C₁:=fun i=>(C (true,i)).1.val
  let u₀:=actualPaddingSpokeHub (m:=m) G.u (fun i=>(C (false,i)).2.val)
  let u₁:=actualPaddingSpokeHub (m:=m) G.u' (fun i=>(C (true,i)).2.val)
  have hmaps:=padded_maps_compatible G.src G.dst G.row G.u G.φ φ' G.ψ ψ' m C₀ C₁
    (fun i=>(C (false,i)).2.val) (fun i=>(C (true,i)).2.val) (G.R∪G.R') G.B
    (fun a=>⟨Finset.mem_union_left _ (G.rimRoots a).1,Finset.mem_union_left _ (G.rimRoots a).2.1⟩)
    (fun s=>Finset.mem_union_left _ (G.spokeRoots s).1) (fun s=>(G.hubRoots s).1) hφ hψ hmap
    (fun i=>by rw [(hh (false,i)).1,(hh (true,i)).1];exact hhmap i)
  have hmapu:∀ s,ψ' (u₀ s)=u₁ s:=by
    intro s
    have he:=hmaps.2.2.2 s
    simpa only [←G.hubMap] using he
  have hrgeo:=marked_paired_padding_root_geometry G.src G.dst G.row G.φ φ' G.R G.R' hm C v p
    (fun j i k=>hC (j,i) k) hv hφ hmap G.rimRoots G.spokeRoots G.sourceArcSeparation G.imageArcSeparation
    G.fourRootSeparation hpair (fun i k=>(hav i k).2) hsep
  have hbal:=padding_row_balance G.src G.dst G.row G.jr G.js m C₀ G.rowBalance G.markedRowBalance
  have hr₀:∀ a,if G.jr a then ∃ k,ktail k=G.src a∧khead k=G.dst a else ∃ e,tail e=G.src a∧head e=G.dst a:=by
    intro a;have hh:=G.rimPresent a;cases hj:G.jr a <;> simp only [hj,Bool.false_eq_true,ite_false,ite_true] at hh ⊢
    all_goals exact hh.1
  have hr₁:∀ a,if G.jr a then ∃ k,ktail k=G.φ (G.src a)∧khead k=G.φ (G.dst a)
      else ∃ e,tail e=G.φ (G.src a)∧head e=G.φ (G.dst a):=by
    intro a;have hh:=G.rimPresent a;cases hj:G.jr a <;> simp only [hj,Bool.false_eq_true,ite_false,ite_true] at hh ⊢
    all_goals exact hh.2
  have hs₀:∀ s,if G.js s then HK (G.row s) (G.u s) else H₀ (G.row s) (G.u s):=by
    intro s;have hh:=G.spokePresent s;cases hj:G.js s <;> simp only [hj,Bool.false_eq_true,ite_false,ite_true] at hh ⊢
    all_goals exact hh.1
  have hs₁:∀ s,if G.js s then HK (G.φ (G.row s)) (G.u' s) else H₀ (G.φ (G.row s)) (G.u' s):=by
    intro s;have hh:=G.spokePresent s;cases hj:G.js s <;> simp only [hj,Bool.false_eq_true,ite_false,ite_true] at hh ⊢
    all_goals exact hh.2
  have ht₀:=padded_typed_presence G.src G.dst G.row G.jr G.js G.u (fun i=>C (false,i)) hr₀ hs₀
  have ht₁:=padded_typed_presence (fun a=>G.φ (G.src a)) (fun a=>G.φ (G.dst a)) (fun s=>G.φ (G.row s)) G.jr G.js G.u'
    (fun i=>C (true,i)) hr₁ hs₁
  have havoid:∀ i,Disjoint (markedWheelPhysicalResources (C i)) (G.source∪G.image):=by
    intro i
    apply marked_padding_avoids_old_resources hm hp (C i) (if i.1 then G.φ (v i.2) else v i.2) (p i)
      (G.R∪G.R') G.B (hC i) (fun k=>(hav i k).1) (by rw [(hh i).1];exact (hh i).2) (G.source∪G.image)
    intro e he;cases e with
    | inl e=>exact G.old_resources _ he
    | inr vu=>exact (G.old_resources _ he).2
  have hinj₀:=padded_graph_occurrences_injective G.src G.dst G.row G.jr G.u hp (fun i=>C (false,i))
    (fun i j hij=>hpack (false,i) (false,j) (fun he=>hij (congrArg Prod.snd he)))
    (fun i=>(havoid (false,i)).mono_right Finset.subset_union_left) G.sourceRimInjective G.sourceSpokeInjective
  have hinj₁:=padded_graph_occurrences_injective (fun a=>G.φ (G.src a)) (fun a=>G.φ (G.dst a))
    (fun s=>G.φ (G.row s)) G.jr G.u' hp (fun i=>C (true,i))
    (fun i j hij=>hpack (true,i) (true,j) (fun he=>hij (congrArg Prod.snd he)))
    (fun i=>(havoid (true,i)).mono_right Finset.subset_union_right) G.imageRimInjective G.imageSpokeInjective
  refine {
    src:=paddingRimTail G.src C₀
    dst:=paddingRimHead G.dst C₀
    row:=paddingSpokeRow G.row C₀
    φ:=φ'
    ψ:=ψ'
    u:=u₀
    u':=u₁
    jr:=paddingRimType G.jr m
    js:=paddingSpokeType G.js m
    R:=G.R∪pairedPaddingPrivateRows p false
    R':=G.R'∪pairedPaddingPrivateRows p true
    B:=G.B∪Finset.univ.image h
    disjointRows:=(paired_padding_root_sets p G.R G.R' G.disjointRows (fun i k=>(hav i k).1) hdis).1
    rimRoots:=hrgeo.1
    spokeRoots:=hrgeo.2.1
    hubRoots:=?_
    hubMap:=fun s=>(hmapu s).symm
    differentHubs:=?_
    sourceArcSeparation:=hrgeo.2.2.1
    imageArcSeparation:=hrgeo.2.2.2.1
    fourRootSeparation:=hrgeo.2.2.2.2
    rowBalance:=hbal.1
    markedRowBalance:=hbal.2
    hubBalance:=actual_padding_hub_balance G.u (fun i=>(C (false,i)).2.val) G.js m G.hubBalance
    sourceRimInjective:=hinj₀.1
    imageRimInjective:=?_
    sourceSpokeInjective:=hinj₀.2
    imageSpokeInjective:=?_
    rimPresent:=?_
    spokePresent:=?_}
  · rintro (s|⟨i,k⟩)
    · exact ⟨Finset.mem_union_left _ (G.hubRoots s).1,Finset.mem_union_left _ (G.hubRoots s).2⟩
    · exact ⟨Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(false,i),Finset.mem_univ _,(hh (false,i)).1.symm⟩),
        Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(true,i),Finset.mem_univ _,(hh (true,i)).1.symm⟩)⟩
  · rintro (s|⟨i,k⟩)
    · exact G.differentHubs s
    · change (C (false,i)).2.val≠(C (true,i)).2.val
      rw [(hh (false,i)).1,(hh (true,i)).1]
      intro he;have hj:=congrArg Prod.fst (h.injective he);simp at hj
  · simpa only [hmaps.1,hmaps.2.1] using hinj₁.1
  · simpa only [hmaps.2.2.1] using hinj₁.2
  · intro a
    have h₀:=ht₀.1 a
    have h₁:=ht₁.1 a
    dsimp only [C₀,C₁] at *
    simp only [hmaps.1,hmaps.2.1]
    cases hj:paddingRimType G.jr m a <;> simp only [hj,Bool.false_eq_true,ite_false,ite_true] at h₀ h₁ ⊢
    all_goals exact ⟨h₀,h₁⟩
  · intro s
    have h₀:=ht₀.2 s
    have h₁:=ht₁.2 s
    dsimp only [C₀,C₁,u₀,u₁] at *
    simp only [hmaps.2.2.1]
    cases hj:paddingSpokeType G.js m s <;> simp only [hj,Bool.false_eq_true,ite_false,ite_true] at h₀ h₁ ⊢
    all_goals exact ⟨h₀,h₁⟩

end Oberwolfach
