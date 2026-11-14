module

public import Oberwolfach.MarkedSampledOutsideCover
public import Oberwolfach.MarkedOutsideArcRestriction
public import Oberwolfach.MarkedCoverPackingAvoidance

@[expose] public section

/-! The original boundary sample constructs a packing for every later
sparse outside subgraph. Both path and hub counts come from one event;
the prescribed subgraph can be chosen after that event is revealed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_sampled_outside_cover_original (l:ℕ) (hl:2≤l) (β p:ℝ) (hβ:0<β) (hp:0<p) (hp1:p≤1)
    (η:ℝ) (hη:0<η) (hη1:η≤1) (hscale:100*((l:ℝ)+20)*η≤p^3*β/2)
    (b:ℕ) (hb:1≤b) (q:ℕ):
    ∃ N:ℕ,∀ (V U E K:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
    N≤Fintype.card V→∀ (tail head:E→V) (ktail khead:K→V)
      (H₀ HK:V→U→Prop) (π:Equiv.Perm V) (X:Finset V) (Z:Finset U),
    Function.Injective (markedPhysicalEdge tail head ktail khead π)→(∀ x,π x∈X↔x∈X)→
    (∀ j x u,β*Fintype.card (V⊕U)≤((X.filter (fun z=>markedArcPresent tail head ktail khead j x z∧
      (if j then HK z u else H₀ z u))).card:ℝ))→
    (∀ j x y u,x≠(if j then π y else y)→β*Fintype.card (V⊕U)≤
      ((X.filter (fun z=>markedArcPresent tail head ktail khead false x z∧
        markedArcPresent tail head ktail khead j z y∧H₀ z u)).card:ℝ))→
    1-2/(Fintype.card (V⊕U):ℝ)^q≤
      (FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1)).probability
        (fun σ=>
    ∀ (A:Finset (E⊕K)) (S:Finset (V×U)),
    (A.card:ℝ)≤η^2*(Fintype.card V:ℝ)^2→(S.card:ℝ)≤η^2*(Fintype.card V:ℝ)^2→
    (∀ a∈A,Sum.elim tail ktail a∉X∧Sum.elim head khead a∉X)→
    (∀ a∈A,¬PermutationClose π b (Sum.elim tail ktail a) (Sum.elim head khead a))→
    (∀ v,((A.filter (fun a=>v=Sum.elim tail ktail a∨v=Sum.elim head khead a)).card:ℝ)≤η^2*Fintype.card V)→
    (∀ a∈A,β*Fintype.card (V⊕U)≤((Z.filter (fun u=>H₀ (Sum.elim tail ktail a) u∧
      (if markedArcType a then HK (Sum.elim head khead a) u else H₀ (Sum.elim head khead a) u))).card:ℝ))→
    (∀ z∈S,z.1∉X∧z.2∉Z∧(H₀ z.1 z.2∨HK z.1 z.2))→
    (∀ v,((S.filter (fun z=>v=z.1)).card:ℝ)≤η^2*Fintype.card V)→
    (∀ u,((S.filter (fun z=>z.2=u)).card:ℝ)≤η^2*Fintype.card V)→
    ∃ M:Finset (MarkedWheel tail head ktail khead (l+4) π b H₀ HK),
      (∀ W∈M,∀ Z∈M,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))∧
      (M.biUnion markedWheelPhysicalResources).filter (markedInnerResource (Xᶜ) (Zᶜ))=
        A.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S.image Sum.inr∧
      (∀ v,((markedPackingRimGraph M).degree v:ℝ)≤24*η*Fintype.card V)∧
      (∀ v,((Finset.univ.filter (markedPackingSpokes M v)).card:ℝ)≤6*η*Fintype.card V)∧
      (∀ u,((Finset.univ.filter (fun v=>markedPackingSpokes M v u)).card:ℝ)≤3*(l+5)*η*Fintype.card V)∧
      (∀ B:Finset (Finset V⊕(V×U)),
        (∀ j x y,markedBoundaryRimAllowed π X σ j x y→
          Sum.inl (if j then ({x,π y}:Finset V) else {x,y})∉B)→
        (∀ x u,markedBoundarySpokeAllowed X Z σ x u→Sum.inr (x,u)∉B)→
        Disjoint (A.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S.image Sum.inr) B→
        Disjoint (M.biUnion markedWheelPhysicalResources) B)) :=by
  obtain ⟨N,hN⟩:=marked_sampled_outside_cover l hl β p hβ hp hp1 η hη hη1 hscale b hb q
  refine ⟨N,?_⟩
  intro V U E K _ _ _ _ hn tail head ktail khead H₀ HK π X Z hphys hX hstep hjoin
  classical
  have hevent:=hN V U E K hn tail head ktail khead H₀ HK π X Z hphys hX hstep hjoin
  apply hevent.trans
  apply finiteLaw_probability_mono
  intro σ hσ A S hAc hSc hArows hAsep hAdeg hhubs hS hSr hSc'
  let PE:=fun e:E=>markedCoverRimAllowed π X σ false (tail e) (head e)
  let PK:=fun e:K=>markedCoverRimAllowed π X σ true (ktail e) (khead e)
  let E':={e:E//PE e}
  let K':={e:K//PK e}
  let t':=fun e:E'=>tail e.val
  let h':=fun e:E'=>head e.val
  let kt':=fun e:K'=>ktail e.val
  let kh':=fun e:K'=>khead e.val
  obtain ⟨f,hf,hforget⟩:=marked_outside_arc_restriction tail head ktail khead π X σ A hArows
  let A':=Finset.univ.image f
  have htail (a:A):Sum.elim t' kt' (f a)=Sum.elim tail ktail a.val:=by
    rw [←hforget a];cases f a <;> rfl
  have hhead (a:A):Sum.elim h' kh' (f a)=Sum.elim head khead a.val:=by
    rw [←hforget a];cases f a <;> rfl
  have htype (a:A):markedArcType (f a)=markedArcType a.val:=by
    rw [←hforget a];cases f a <;> rfl
  have hphysical (a:A):markedPhysicalEdge t' h' kt' kh' π (f a)=markedPhysicalEdge tail head ktail khead π a.val:=
    marked_physical_edge_eq_of_endpoints_and_type π a.val (f a) (htail a) (hhead a) (htype a)
  have hcard:A'.card=A.card:=by
    rw [Finset.card_image_of_injective _ hf,Finset.card_univ,Fintype.card_coe]
  have hArows':∀ a∈A',Sum.elim t' kt' a∉X∧Sum.elim h' kh' a∉X:=by
    intro a ha;obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp ha
    rw [htail,hhead];exact hArows v.val v.property
  have hAsep':∀ a∈A',¬PermutationClose π b (Sum.elim t' kt' a) (Sum.elim h' kh' a):=by
    intro a ha;obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp ha
    rw [htail,hhead];exact hAsep v.val v.property
  have hAdeg':∀ v,((A'.filter (fun a=>v=Sum.elim t' kt' a∨v=Sum.elim h' kh' a)).card:ℝ)≤η^2*Fintype.card V:=by
    intro v
    have he:(A'.filter (fun a=>v=Sum.elim t' kt' a∨v=Sum.elim h' kh' a)).card=
        (A.filter (fun a=>v=Sum.elim tail ktail a∨v=Sum.elim head khead a)).card:=by
      convert finite_subtype_image_filter_card A f hf
        (fun a=>v=Sum.elim t' kt' a∨v=Sum.elim h' kh' a)
        (fun a=>v=Sum.elim tail ktail a∨v=Sum.elim head khead a)
        (fun a=>by rw [htail,hhead]) using 1 <;> congr!
    rw [he];exact hAdeg v
  have hhubs':∀ a∈A',β*Fintype.card (V⊕U)≤((Z.filter (fun u=>H₀ (Sum.elim t' kt' a) u∧
      (if markedArcType a then HK (Sum.elim h' kh' a) u else H₀ (Sum.elim h' kh' a) u))).card:ℝ):=by
    intro a ha;obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp ha
    simp only [htail,hhead,htype]
    exact hhubs v.val v.property
  obtain ⟨M,hM,hMI,hr,hs,hc⟩:=hσ A' S (by rw [hcard];exact hAc) hSc hArows' hAsep' hAdeg' hhubs' hS hSr hSc'
  let lift:MarkedWheel t' h' kt' kh' (l+4) π b
      (fun x u=>H₀ x u∧markedCoverSpokeAllowed X Z σ x u)
      (fun x u=>HK x u∧markedCoverSpokeAllowed X Z σ x u)→
      MarkedWheel tail head ktail khead (l+4) π b H₀ HK:=
    markedWheelToLarger PE PK (fun _ _ h=>h.1) (fun _ _ h=>h.1)
  let M':=M.image lift
  have hres:M'.biUnion markedWheelPhysicalResources=M.biUnion markedWheelPhysicalResources:=
    markedWheelToLarger_cover PE PK _ _ M
  have hreq:A'.image (fun a=>(Sum.inl (markedPhysicalEdge t' h' kt' kh' π a):Finset V⊕(V×U)))=
      A.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a)):=by
    ext e
    simp only [A',Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨_,⟨a,rfl⟩,he⟩
      exact ⟨a.val,a.property,by rw [←hphysical a];exact he⟩
    · rintro ⟨a,ha,he⟩
      exact ⟨f ⟨a,ha⟩,⟨⟨a,ha⟩,rfl⟩,by rw [hphysical];exact he⟩
  have hrim:markedPackingRimGraph M'=markedPackingRimGraph M:=marked_packing_lift_rim PE PK _ _ M
  have hsp:markedPackingSpokes M'=markedPackingSpokes M:=marked_packing_lift_spokes PE PK _ _ M
  refine ⟨M',markedWheelToLarger_matching PE PK _ _ M hM,?_,?_,?_,?_,?_⟩
  · rw [hres,hMI,hreq]
  · intro v;rw [hrim];exact hr v
  · intro v;rw [hsp];exact hs v
  · intro u;rw [hsp];exact hc u
  · intro B hBr hBs hBA
    rw [hres]
    apply marked_cover_packing_avoids_earlier tail head ktail khead H₀ HK π (l+4) b X Z hX σ B _ hBr hBs hBA M
    rw [hMI,hreq]
end Oberwolfach
