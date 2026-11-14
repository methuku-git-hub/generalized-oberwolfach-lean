module

public import Oberwolfach.MarkedSampledOutsideCoverOriginal
public import Oberwolfach.MarkedBoundaryCoverScales
public import Oberwolfach.PhysicalHostDegreeBounds

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

theorem marked_sampled_small_outside_cover (l:ℕ) (hl:2≤l) (β ν:ℝ) (hβ:0<β) (hν:0<ν) (q:ℕ):
    ∃ p₀:ℝ,0<p₀∧∀ (p:ℝ) (hp:0<p) (hp1:p≤1),p≤p₀→∀ (b:ℕ),1≤b→
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
    (A.card:ℝ)≤p^9*(Fintype.card V:ℝ)^2→(S.card:ℝ)≤p^9*(Fintype.card V:ℝ)^2→
    (∀ a∈A,Sum.elim tail ktail a∉X∧Sum.elim head khead a∉X)→
    (∀ a∈A,¬PermutationClose π b (Sum.elim tail ktail a) (Sum.elim head khead a))→
    (∀ v,((A.filter (fun a=>v=Sum.elim tail ktail a∨v=Sum.elim head khead a)).card:ℝ)≤p^9*Fintype.card V)→
    (∀ a∈A,β*Fintype.card (V⊕U)≤((Z.filter (fun u=>H₀ (Sum.elim tail ktail a) u∧
      (if markedArcType a then HK (Sum.elim head khead a) u else H₀ (Sum.elim head khead a) u))).card:ℝ))→
    (∀ z∈S,z.1∉X∧z.2∉Z∧(H₀ z.1 z.2∨HK z.1 z.2))→
    (∀ v,((S.filter (fun z=>v=z.1)).card:ℝ)≤p^9*Fintype.card V)→
    (∀ u,((S.filter (fun z=>z.2=u)).card:ℝ)≤p^9*Fintype.card V)→
    ∃ M:Finset (MarkedWheel tail head ktail khead (l+4) π b H₀ HK),
      (∀ W∈M,∀ Z∈M,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))∧
      (M.biUnion markedWheelPhysicalResources).filter (markedInnerResource (Xᶜ) (Zᶜ))=
        A.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S.image Sum.inr∧
      (∀ v,((markedPackingRimGraph M).degree v:ℝ)≤24*p^4*Fintype.card V)∧
      (∀ v,((Finset.univ.filter (markedPackingSpokes M v)).card:ℝ)≤6*p^4*Fintype.card V)∧
      (∀ u,((Finset.univ.filter (fun v=>markedPackingSpokes M v u)).card:ℝ)≤3*(l+5)*p^4*Fintype.card V)∧
      (∀ z,((ordinaryPhysicalGraph (markedPackingRimGraph M) (markedPackingSpokes M)).degree z:ℝ)≤p^3*Fintype.card V)∧
      (∀ z,((ordinaryPhysicalGraph (markedPackingRimGraph M) (markedPackingSpokes M)).degree z:ℝ)≤ν*p^3*Fintype.card V)∧
      (∀ B:Finset (Finset V⊕(V×U)),
        (∀ j x y,markedBoundaryRimAllowed π X σ j x y→
          Sum.inl (if j then ({x,π y}:Finset V) else {x,y})∉B)→
        (∀ x u,markedBoundarySpokeAllowed X Z σ x u→Sum.inr (x,u)∉B)→
        Disjoint (A.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S.image Sum.inr) B→
        Disjoint (M.biUnion markedWheelPhysicalResources) B)) :=by
  obtain ⟨p₀,hp₀,hscale⟩:=marked_boundary_cover_scale_choices l β ν hβ hν
  refine ⟨p₀,hp₀,?_⟩
  intro p hp hp1 hsmall b hb
  obtain ⟨_,hη1,hηscale,hpow,hC,hCν⟩:=hscale p hp hsmall
  obtain ⟨N,hN⟩:=marked_sampled_outside_cover_original l hl β p hβ hp hp1 (p^4) (by positivity) hη1 hηscale b hb q
  refine ⟨N,?_⟩
  intro V U E K _ _ _ _ hn tail head ktail khead H₀ HK π X Z hphys hX hstep hjoin
  have hevent:=hN V U E K hn tail head ktail khead H₀ HK π X Z hphys hX hstep hjoin
  apply hevent.trans
  apply finiteLaw_probability_mono
  intro σ hσ A S hAc hSc hArows hAsep hAdeg hhubs hS hSr hSc'
  have hlin:p^9*Fintype.card V≤(p^4)^2*Fintype.card V:=
    mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _)
  have hquad:p^9*(Fintype.card V:ℝ)^2≤(p^4)^2*(Fintype.card V:ℝ)^2:=
    mul_le_mul_of_nonneg_right hpow (sq_nonneg _)
  obtain ⟨M,hM,hI,hr,hs,hc,havoid⟩:=hσ A S (hAc.trans hquad) (hSc.trans hquad)
    hArows hAsep (fun v=>(hAdeg v).trans hlin) hhubs hS (fun v=>(hSr v).trans hlin) (fun u=>(hSc' u).trans hlin)
  have hd:∀ z,((ordinaryPhysicalGraph (markedPackingRimGraph M) (markedPackingSpokes M)).degree z:ℝ)≤
      (30+3*((l:ℝ)+5))*p^4*Fintype.card V:=by
    apply ordinary_physical_degree_bound _ _ _ _ _ _ hr hs hc
    · have hn:(0:ℝ)≤Fintype.card V:=Nat.cast_nonneg _
      have h:0≤3*((l:ℝ)+5)*p^4*Fintype.card V:=by positivity
      nlinarith only [h]
    · have h:0≤30*p^4*Fintype.card V:=by positivity
      nlinarith only [h]
  refine ⟨M,hM,hI,hr,hs,hc,?_,?_,havoid⟩
  · intro z;exact (hd z).trans (mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg _))
  · intro z;exact (hd z).trans (mul_le_mul_of_nonneg_right hCν (Nat.cast_nonneg _))
end Oberwolfach
