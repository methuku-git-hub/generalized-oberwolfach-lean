module

public import Oberwolfach.MarkedFixedAttachmentWheels
public import Oberwolfach.FiniteConflictSeparatedChoices

@[expose] public section

/-! All vertex-wheel pairs through their already assigned attachment vertices.
Only the internal vertices are chosen; the fixed endpoints are never resampled. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K I:Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

 theorem marked_fixed_attachment_families
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop)
    (π:Equiv.Perm V) (b l:ℕ) (hl:2≤l) (v v' a z:I→V) (u:I→U) (j:I→Bool)
    (W Z A₀:Finset V) (hAZ:Disjoint A₀ Z)
    (hroots:∀ i,v i∈Z∧v' i∈Z) (ha:∀ i,a i∈A₀) (hz:∀ i,z i∈A₀)
    (haz:∀ i,a i≠z i)
    (hend:∀ i k,i≠k→Disjoint ({a i,z i}:Finset V) {a k,z k})
    (hAA:∀ x∈A₀,∀ y∈A₀,x≠y→¬PermutationClose π b x y)
    (hAF:∀ x∈A₀,∀ y∈Z,¬PermutationClose π b x y)
    (hsp:∀ i,H₀ (a i) (u i)∧H₀ (z i) (u i))
    (hroot:∀ i,if j i then HK (v i) (u i)∧HK (v' i) (u i) else H₀ (v i) (u i)∧H₀ (v' i) (u i))
    (hopen:∀ i,(∃ e,tail e=v i∧head e=a i)∧(∃ e,tail e=v' i∧head e=a i))
    (hclose:∀ i,if j i then (∃ e,ktail e=z i∧khead e=v i)∧(∃ e,ktail e=z i∧khead e=v' i)
      else (∃ e,tail e=z i∧head e=v i)∧(∃ e,tail e=z i∧head e=v' i))
    (c:ℝ)
    (hstep:∀ i,∀ t:Bool,∀ x,c≤((Finset.univ.filter (fun y=>
      (if t then ∃ e,ktail e=x∧khead e=y else ∃ e,tail e=x∧head e=y)∧
      (if t then HK y (u i) else H₀ y (u i)))).card:ℝ))
    (hjoin:∀ i,∀ x y,x≠y→c≤((Finset.univ.filter (fun q=>(∃ e,tail e=x∧head e=q)∧
      (∃ e,tail e=q∧head e=y)∧H₀ q (u i))).card:ℝ))
    (hbudget:W.card+((Fintype.card I:ℝ)*(l+3)+Z.card+A₀.card+l+4)*(2*b+1)<c):
    ∃ p:I→(Fin (l+3)↪V),∃ C D:I→MarkedWheel tail head ktail khead (l+3) π b H₀ HK,
      (∀ i,p i 0=a i∧p i (Fin.last (l+2))=z i∧(C i).2.val=u i∧(D i).2.val=u i)∧
      (∀ i x,(C i).1.val x=rootedCycleOrder (markedRootOrder (l+3) (j i)) (v i) (p i) x)∧
      (∀ i x,(D i).1.val x=rootedCycleOrder (markedRootOrder (l+3) (j i)) (v' i) (p i) x)∧
      (∀ i x,p i x∉Z∧∀ y∈Z,¬PermutationClose π b (p i x) y)∧
      (∀ i x,p i x∈W→p i x∈({a i,z i}:Finset V))∧
      (∀ i,PermutationSeparated π b (p i))∧
      (∀ i k,i≠k→Disjoint (Finset.univ.image (p i)) (Finset.univ.image (p k)))∧
      (∀ i k,∀ x y,p i x≠p k y→¬PermutationClose π b (p i x) (p k y))∧
      ∀ i x,∀ y∈A₀,p i x≠y→¬PermutationClose π b (p i x) y:=by
  let F:=permutationConflictGraph π b
  have hF:∀ x,(F.degree x:ℝ)≤2*b:=by intro x;exact_mod_cast permutationConflictGraph_degree_le π b x
  let Q:=(Fin (l+3)↪V)×
    (MarkedWheel tail head ktail khead (l+3) π b H₀ HK×MarkedWheel tail head ktail khead (l+3) π b H₀ HK)
  let S:Q→Finset V:=fun q=>(Finset.univ.image q.1)\A₀
  let Good:I→Q→Prop:=fun i q=>
    (q.1 0=a i∧q.1 (Fin.last (l+2))=z i∧q.2.1.2.val=u i∧q.2.2.2.val=u i)∧
    (∀ x,q.2.1.1.val x=rootedCycleOrder (markedRootOrder (l+3) (j i)) (v i) q.1 x)∧
    (∀ x,q.2.2.1.val x=rootedCycleOrder (markedRootOrder (l+3) (j i)) (v' i) q.1 x)∧
    (∀ x,q.1 x∉Z∧∀ y∈Z,¬PermutationClose π b (q.1 x) y)∧
    (∀ x,q.1 x∈A₀→q.1 x∈({a i,z i}:Finset V))∧
    (∀ x,∀ y∈A₀,q.1 x≠y→¬PermutationClose π b (q.1 x) y)∧
    PermutationSeparated π b q.1
  have hchoose:∀ i,∀ B:Finset V,(B.card:ℝ)≤W.card+Fintype.card I*(l+3)*(2*b+1)→
      ∃ q,Good i q∧(S q).card≤l+3∧Disjoint (S q) B:=by
    intro i B hB
    let T:Finset V:={a i,z i}
    let W':=B\T
    let Z':=Z∪(A₀\T)
    have haT:a i∈T:=by simp [T]
    have hzT:z i∈T:=by simp [T]
    have hTZ:T⊆A₀:=by intro x hx;rcases Finset.mem_insert.mp hx with rfl|hx;exact ha i;exact (Finset.mem_singleton.mp hx).symm ▸ hz i
    have hZ':(Z'.card:ℝ)≤Z.card+A₀.card:=by
      exact_mod_cast (Finset.card_union_le Z (A₀\T)).trans (Nat.add_le_add_left (Finset.card_le_card Finset.sdiff_subset) Z.card)
    have hW':(W'.card:ℝ)≤B.card:=by exact_mod_cast Finset.card_le_card (Finset.sdiff_subset (s:=B) (t:=T))
    have hbd:(W'.card:ℝ)+(Z'.card+l+4)*(2*b+1)<c:=by nlinarith only [hbudget,hB,hZ',hW']
    have hsep (x:V) (hx:x∈T):∀ y∈Z',¬PermutationClose π b x y:=by
      intro y hy
      rcases Finset.mem_union.mp hy with hy|hy
      · exact hAF x (hTZ hx) y hy
      · exact hAA x (hTZ hx) y (Finset.mem_sdiff.mp hy).1
          (fun he=>(Finset.mem_sdiff.mp hy).2 (he ▸ hx))
    have hnotZ (x:V) (hx:x∈T):x∉Z':=by
      intro hh
      rcases Finset.mem_union.mp hh with hh|hh
      · exact Finset.disjoint_left.mp hAZ (hTZ hx) hh
      · exact (Finset.mem_sdiff.mp hh).2 hx
    obtain ⟨p,C,D,hp0,hplast,hCu,hDu,hC,hD,hav,hps⟩:=marked_fixed_attachment_wheels
      tail head ktail khead H₀ HK π b l hl (v i) (v' i) (a i) (z i) (u i) (j i) W' Z'
      (Finset.mem_union_left _ (hroots i).1) (Finset.mem_union_left _ (hroots i).2)
      (by simp [W',T]) (by simp [W',T]) (hnotZ _ haT) (hnotZ _ hzT)
      (hAA _ (ha i) _ (hz i) (haz i)) (hsep _ haT) (hsep _ hzT)
      (hsp i) (hroot i) (hopen i) (hclose i) c (hstep i) (hjoin i) hbd
    have hpa:∀ x,p x∈A₀→p x∈T:=by
      intro x hx
      by_contra hn
      exact (hav x).2.1 (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx,hn⟩))
    have hpT:∀ x∈T,∃ k,p k=x:=by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl|hx
      · exact ⟨0,hp0⟩
      · have he:x=z i:=Finset.mem_singleton.mp hx
        exact ⟨Fin.last _,hplast.trans he.symm⟩
    have hpA:∀ x,∀ y∈A₀,p x≠y→¬PermutationClose π b (p x) y:=by
      intro x y hy hxy
      by_cases ht:y∈T
      · obtain ⟨k,rfl⟩:=hpT y ht
        exact hps x k (fun he=>hxy (congrArg p he))
      · exact (hav x).2.2 y (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hy,ht⟩))
    refine ⟨⟨p,C,D⟩,⟨⟨hp0,hplast,hCu,hDu⟩,hC,hD,?_,hpa,hpA,hps⟩,?_,?_⟩
    · intro x
      exact ⟨fun hx=>(hav x).2.1 (Finset.mem_union_left _ hx),
        fun y hy=>(hav x).2.2 y (Finset.mem_union_left _ hy)⟩
    · exact (Finset.card_le_card Finset.sdiff_subset).trans (by simpa only [Fintype.card_fin,Finset.card_univ] using (Finset.card_image_le (f:=(p:Fin (l+3)→V)) (s:=Finset.univ)))
    · apply Finset.disjoint_left.mpr
      intro x hx hxB
      obtain ⟨hx,hxA⟩:=Finset.mem_sdiff.mp hx
      obtain ⟨k,_,rfl⟩:=Finset.mem_image.mp hx
      exact (hav k).1 (Finset.mem_sdiff.mpr ⟨hxB,fun ht=>hxA (hTZ ht)⟩)
  obtain ⟨q,hq,hd⟩:=finite_conflict_separated_choices S Good W (l+3) F (2*b) (by positivity) hF
    (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hchoose)
  have hgood:∀ i,Good i (q i):=fun i=>(hq i).1
  have hint (i:I) (x:Fin (l+3)) (hx:(q i).1 x∉A₀):(q i).1 x∈S (q i):=
    Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩,hx⟩
  have hdis:∀ i k,i≠k→Disjoint (Finset.univ.image (q i).1) (Finset.univ.image (q k).1):=by
    intro i k hik
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨x₀,_,rfl⟩:=Finset.mem_image.mp hx
    obtain ⟨y₀,_,he⟩:=Finset.mem_image.mp hy
    by_cases ha₀:(q i).1 x₀∈A₀
    · have ha₁:(q k).1 y₀∈A₀:=he.symm ▸ ha₀
      exact Finset.disjoint_left.mp (hend i k hik) ((hgood i).2.2.2.2.1 x₀ ha₀)
        (he ▸ (hgood k).2.2.2.2.1 y₀ ha₁)
    · have ha₁:(q k).1 y₀∉A₀:=he.symm ▸ ha₀
      exact Finset.disjoint_left.mp (hd i k hik).1 (hint i x₀ ha₀) (he ▸ hint k y₀ ha₁)
  refine ⟨fun i=>(q i).1,fun i=>(q i).2.1,fun i=>(q i).2.2,
    fun i=>(hgood i).1,fun i=>(hgood i).2.1,fun i=>(hgood i).2.2.1,
    fun i=>(hgood i).2.2.2.1,?_,fun i=>(hgood i).2.2.2.2.2.2,hdis,?_,fun i=>(hgood i).2.2.2.2.2.1⟩
  · intro i x hx
    by_cases hxA:(q i).1 x∈A₀
    · exact (hgood i).2.2.2.2.1 x hxA
    · exact False.elim (Finset.disjoint_left.mp (hq i).2.2 (hint i x hxA) hx)
  · intro i k x y hxy
    by_cases hi:i=k
    · subst k
      exact (hgood i).2.2.2.2.2.2 x y (fun he=>hxy (congrArg (q i).1 he))
    · by_cases hyA:(q k).1 y∈A₀
      · exact (hgood i).2.2.2.2.2.1 x _ hyA hxy
      · by_cases hxA:(q i).1 x∈A₀
        · intro hc
          exact (hgood k).2.2.2.2.2.1 y _ hxA hxy.symm ((permutationClose_symm π b _ _).mp hc)
        · intro hc
          exact (hd i k hi).2 _ (hint i x hxA) _ (hint k y hyA) ⟨hxy,hc⟩

end Oberwolfach
