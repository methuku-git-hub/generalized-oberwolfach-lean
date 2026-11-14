module

public import Oberwolfach.MarkedSampledSmallOutsideCoverFive
public import Oberwolfach.MarkedSampledSmallOutsideCover
public import Oberwolfach.MarkedRestrictedUnusedBounds
public import Oberwolfach.MarkedReservationComplement

@[expose] public section

/-! The same boundary sample completes the actual outside remainder of
any later approximate packing in the complementary host. The earlier
packing may have large degree. Every outside resource is covered exactly
once when its packing is combined with the constructed disjoint packing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_sampled_outside_completion_five (β ν:ℝ) (hβ:0<β) (hν:0<ν) (q:ℕ):
    ∃ p₀:ℝ,0<p₀∧∀ (p:ℝ) (hp:0<p) (hp1:p≤1),p≤p₀→∀ (b:ℕ),1≤b→
    ∃ N:ℕ,∀ (V U E K:Type) [Fintype V] [Fintype U] [Fintype E] [Fintype K]
      [DecidableEq V] [DecidableEq U],
    N≤Fintype.card V→∀ (tail head:E→V) (ktail khead:K→V)
      (H₀ HK:V→U→Prop) (π:Equiv.Perm V) (X:Finset V) (Z:Finset U),
    Function.Injective (markedPhysicalEdge tail head ktail khead π)→(∀ x,π x∈X↔x∈X)→
    (∀ j x u,β*Fintype.card (V⊕U)≤((X.filter (fun z=>markedArcPresent tail head ktail khead j x z∧
      (if j then HK z u else H₀ z u))).card:ℝ))→
    (∀ j x y u,x≠(if j then π y else y)→β*Fintype.card (V⊕U)≤
      ((X.filter (fun z=>markedArcPresent tail head ktail khead false x z∧
        markedArcPresent tail head ktail khead j z y∧H₀ z u)).card:ℝ))→
    (∀ a:E⊕K,Sum.elim tail ktail a∉X→Sum.elim head khead a∉X→
      ¬PermutationClose π b (Sum.elim tail ktail a) (Sum.elim head khead a))→
    (∀ a:E⊕K,Sum.elim tail ktail a∉X→Sum.elim head khead a∉X→
      β*Fintype.card (V⊕U)≤((Z.filter (fun u=>H₀ (Sum.elim tail ktail a) u∧
      (if markedArcType a then HK (Sum.elim head khead a) u else H₀ (Sum.elim head khead a) u))).card:ℝ))→
    1-2/(Fintype.card (V⊕U):ℝ)^q≤
      (FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1)).probability
        (fun σ=>
    let PE:=fun e:E=>¬markedBoundaryRimAllowed π X σ false (tail e) (head e)
    let PK:=fun e:K=>¬markedBoundaryRimAllowed π X σ true (ktail e) (khead e)
    let H₀':=fun x u=>H₀ x u∧¬markedBoundarySpokeAllowed X Z σ x u
    let HK':=fun x u=>HK x u∧¬markedBoundarySpokeAllowed X Z σ x u;
    ∀ M₀:Finset (MarkedWheel (fun e:{e//PE e}=>tail e.val) (fun e=>head e.val)
      (fun e:{e//PK e}=>ktail e.val) (fun e=>khead e.val) ((1:ℕ)+4) π b H₀' HK'),
    (∀ x:V⊕U,((markedIncidentEdges (fun e:{e//PE e}=>tail e.val) (fun e=>head e.val)
      (fun e:{e//PK e}=>ktail e.val) (fun e=>khead e.val) π H₀' HK' false x\M₀.biUnion markedActiveResources).card:ℝ)≤p^9*Fintype.card V)→
    ∃ M₁:Finset (MarkedWheel tail head ktail khead ((1:ℕ)+4) π b H₀ HK),
      (∀ W∈M₁,∀ T∈M₁,W≠T→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources T))∧
      Disjoint (M₁.biUnion markedWheelPhysicalResources) (M₀.biUnion markedWheelPhysicalResources)∧
      (∀ a:E⊕K,Sum.elim tail ktail a∉X→Sum.elim head khead a∉X→
        Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈
          M₀.biUnion markedWheelPhysicalResources∪M₁.biUnion markedWheelPhysicalResources)∧
      (∀ x u,x∉X→u∉Z→(H₀ x u∨HK x u)→Sum.inr (x,u)∈
          M₀.biUnion markedWheelPhysicalResources∪M₁.biUnion markedWheelPhysicalResources)∧
      (∀ z,((ordinaryPhysicalGraph (markedPackingRimGraph M₁) (markedPackingSpokes M₁)).degree z:ℝ)≤p^3*Fintype.card V)∧
      (∀ z,((ordinaryPhysicalGraph (markedPackingRimGraph M₁) (markedPackingSpokes M₁)).degree z:ℝ)≤ν*p^3*Fintype.card V)):=by
  classical
  obtain ⟨p₀,hp₀,hN⟩:=marked_sampled_small_outside_cover_five β ν hβ hν q
  refine ⟨p₀,hp₀,?_⟩
  intro p hp hp1 hsmall b hb
  obtain ⟨N,hN⟩:=hN p hp hp1 hsmall b hb
  refine ⟨N,?_⟩
  intro V U E K _ _ _ _ _ _ hn tail head ktail khead H₀ HK π X Z hphys hX hstep hjoin hsep hhubs
  apply (hN V U E K hn tail head ktail khead H₀ HK π X Z hphys hX hstep hjoin).trans
  apply finiteLaw_probability_mono
  intro σ hσ PE PK H₀' HK' M₀ hleft
  let B:=M₀.biUnion markedWheelPhysicalResources
  let A:Finset (E⊕K):=Finset.univ.filter (fun a=>Sum.elim tail ktail a∉X∧Sum.elim head khead a∉X∧
    Sum.inl (markedPhysicalEdge tail head ktail khead π a)∉B)
  let S:Finset (V×U):=Finset.univ.filter (fun z=>z.1∉X∧z.2∉Z∧(H₀ z.1 z.2∨HK z.1 z.2)∧Sum.inr z∉B)
  have hA (a:E⊕K) (ha:a∈A):Sum.elim tail ktail a∉X∧Sum.elim head khead a∉X∧
      Sum.inl (markedPhysicalEdge tail head ktail khead π a)∉B:=(Finset.mem_filter.mp ha).2
  have hS (z:V×U) (hz:z∈S):z.1∉X∧z.2∉Z∧(H₀ z.1 z.2∨HK z.1 z.2)∧Sum.inr z∉B:=
    (Finset.mem_filter.mp hz).2
  have hAkeep (a:E⊕K) (ha:a∈A):Sum.elim PE PK a∧Sum.inl (markedPhysicalEdge tail head ktail khead π a)∉B:=by
    refine ⟨?_,(hA a ha).2.2⟩
    have h:=hA a ha
    cases a <;> simp only [PE,PK,Sum.elim_inl,Sum.elim_inr,markedBoundaryRimAllowed] at h ⊢ <;> tauto
  have hSkeep (z:V×U) (hz:z∈S):(H₀' z.1 z.2∨HK' z.1 z.2)∧Sum.inr z∉B:=by
    have h:=hS z hz
    have hn:¬markedBoundarySpokeAllowed X Z σ z.1 z.2:=by
      simp only [markedBoundarySpokeAllowed];tauto
    exact ⟨h.2.2.1.imp (fun h=>⟨h,hn⟩) (fun h=>⟨h,hn⟩),h.2.2.2⟩
  obtain ⟨hAd,hSr,hSc,hAc,hScard,hdisj⟩:=marked_restricted_unused_bounds (tail:=tail) (head:=head)
    (ktail:=ktail) (khead:=khead) (π:=π) (H₀:=H₀) (HK:=HK) (H₀':=H₀') (HK':=HK') PE PK
    (fun x u (h:H₀' x u)=>h.1) (fun x u (h:HK' x u)=>h.1) M₀ A S (p^9*Fintype.card V) hAkeep hSkeep (by
      intro x
      convert hleft x using 1
      congr 1
      congr 1
      ext e
      simp only [markedIncidentEdges,markedActiveResources,Finset.mem_filter,Finset.mem_sdiff,
        Finset.mem_biUnion,Finset.mem_univ,true_and])
  have hAc':(A.card:ℝ)≤p^9*(Fintype.card V:ℝ)^2:=by nlinarith only [hAc]
  have hSc':(S.card:ℝ)≤p^9*(Fintype.card V:ℝ)^2:=by nlinarith only [hScard]
  obtain ⟨M₁,hM₁,hI,hr,hs,hc,hd,hdν,havoid⟩:=hσ A S hAc' hSc'
    (fun a ha=>⟨(hA a ha).1,(hA a ha).2.1⟩)
    (fun a ha=>hsep a (hA a ha).1 (hA a ha).2.1) hAd
    (fun a ha=>hhubs a (hA a ha).1 (hA a ha).2.1)
    (fun z hz=>⟨(hS z hz).1,(hS z hz).2.1,(hS z hz).2.2.1⟩) (by simpa only [eq_comm] using hSr) (by simpa only [eq_comm] using hSc)
  obtain ⟨hBr,hBs⟩:=marked_reservation_complement_excludes ((1:ℕ)+4) b X Z hX σ M₀
  refine ⟨M₁,hM₁,havoid B hBr hBs hdisj,?_,?_,hd,hdν⟩
  · intro a hax hay
    by_cases ha:Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈B
    · exact Finset.mem_union_left _ ha
    · have hA':a∈A:=Finset.mem_filter.mpr ⟨Finset.mem_univ _,hax,hay,ha⟩
      have hmem:Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈
          A.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S.image Sum.inr:=
        Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,hA',rfl⟩)
      rw [←hI] at hmem
      exact Finset.mem_union_right _ (Finset.mem_filter.mp hmem).1
  · intro x u hx hu hpres
    by_cases he:Sum.inr (x,u)∈B
    · exact Finset.mem_union_left _ he
    · have hz:(x,u)∈S:=Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx,hu,hpres,he⟩
      have hmem:Sum.inr (x,u)∈A.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S.image Sum.inr:=
        Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(x,u),hz,rfl⟩)
      rw [←hI] at hmem
      exact Finset.mem_union_right _ (Finset.mem_filter.mp hmem).1
end Oberwolfach
