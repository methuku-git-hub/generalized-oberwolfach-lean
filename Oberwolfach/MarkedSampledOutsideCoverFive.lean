module

public import Oberwolfach.MarkedOutsideSubgraphPackingFive
public import Oberwolfach.MarkedBoundaryCoverCommonEvent
public import Oberwolfach.MarkedOutsideSubgraphPacking
public import Oberwolfach.MarkedRestrictedLoadIdentities

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

theorem marked_sampled_outside_cover_five (β p:ℝ) (hβ:0<β) (hp:0<p) (hp1:p≤1)
    (η:ℝ) (hη:0<η) (hη1:η≤1) (hscale:100*(((1:ℕ):ℝ)+20)*η≤p^3*β/2)
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
          let P₀:=markedCoverRimAllowed π X σ false
          let P₁:=markedCoverRimAllowed π X σ true
          let E':={e:E//P₀ (tail e) (head e)}
          let K':={e:K//P₁ (ktail e) (khead e)}
          let t':=fun e:E'=>tail e.val
          let h':=fun e:E'=>head e.val
          let kt':=fun e:K'=>ktail e.val
          let kh':=fun e:K'=>khead e.val
          let H₀':=fun x u=>H₀ x u∧markedCoverSpokeAllowed X Z σ x u
          let HK':=fun x u=>HK x u∧markedCoverSpokeAllowed X Z σ x u;
    ∀ (A:Finset (E'⊕K')) (S:Finset (V×U)),
    (A.card:ℝ)≤η^2*(Fintype.card V:ℝ)^2→(S.card:ℝ)≤η^2*(Fintype.card V:ℝ)^2→
    (∀ a∈A,Sum.elim t' kt' a∉X∧Sum.elim h' kh' a∉X)→
    (∀ a∈A,¬PermutationClose π b (Sum.elim t' kt' a) (Sum.elim h' kh' a))→
    (∀ v,((A.filter (fun a=>v=Sum.elim t' kt' a∨v=Sum.elim h' kh' a)).card:ℝ)≤η^2*Fintype.card V)→
    (∀ a∈A,β*Fintype.card (V⊕U)≤((Z.filter (fun u=>H₀ (Sum.elim t' kt' a) u∧
      (if markedArcType a then HK (Sum.elim h' kh' a) u else H₀ (Sum.elim h' kh' a) u))).card:ℝ))→
    (∀ z∈S,z.1∉X∧z.2∉Z∧(H₀ z.1 z.2∨HK z.1 z.2))→
    (∀ v,((S.filter (fun z=>v=z.1)).card:ℝ)≤η^2*Fintype.card V)→
    (∀ u,((S.filter (fun z=>z.2=u)).card:ℝ)≤η^2*Fintype.card V)→
    ∃ M:Finset (MarkedWheel t' h' kt' kh' ((1:ℕ)+4) π b H₀' HK'),
      (∀ W∈M,∀ Z∈M,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))∧
      (M.biUnion markedWheelPhysicalResources).filter (markedInnerResource (Xᶜ) (Zᶜ))=
        A.image (fun a=>Sum.inl (markedPhysicalEdge t' h' kt' kh' π a))∪S.image Sum.inr∧
      (∀ v,((markedPackingRimGraph M).degree v:ℝ)≤24*η*Fintype.card V)∧
      (∀ v,((Finset.univ.filter (markedPackingSpokes M v)).card:ℝ)≤6*η*Fintype.card V)∧
      (∀ u,((Finset.univ.filter (fun v=>markedPackingSpokes M v u)).card:ℝ)≤3*((1:ℕ)+5)*η*Fintype.card V)) :=by
  obtain ⟨N₁,hN₁⟩:=marked_boundary_cover_common_event β p hβ hp hp1 q
  obtain ⟨N₂,hN₂⟩:=marked_sparse_outside_subgraph_packing_five (p^3*β/2) (by positivity) η hη hη1 hscale b hb
  refine ⟨max N₁ N₂,?_⟩
  intro V U E K _ _ _ _ hn tail head ktail khead H₀ HK π X Z hphys hX hstep hjoin
  have hsize:Fintype.card V≤Fintype.card (V⊕U):=by simp
  have hlow:(p^3*β/2)*Fintype.card V≤p^3*β*Fintype.card (V⊕U)/2:=by
    have h:=mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hsize) (by positivity : (0:ℝ)≤p^3*β/2)
    nlinarith only [h]
  have hevent:=hN₁ V U E K (by omega) tail head ktail khead H₀ HK π X Z hstep hjoin
  apply hevent.trans
  apply finiteLaw_probability_mono
  intro σ hσ P₀ P₁ E' K' t' h' kt' kh' H₀' HK' A S hAc hSc hArows hAsep hAdeg hhubs hS hSr hSc'
  apply hN₂ V U E' K' t' h' kt' kh' H₀' HK' π (by omega)
    (markedRestrictedPhysical_injective _ _ hphys) X Z hX
    (fun u j x=>by apply hlow.trans;convert hσ.1 j x u using 1 <;> congr!)
    (fun u j x y hxy=>by apply hlow.trans;convert hσ.2.1 j x y u hxy using 1 <;> congr!)
    A S hAc hSc hArows hAsep hAdeg
    (fun a ha=>by apply hlow.trans;convert hσ.2.2 _ _ _ (hhubs a ha) using 1 <;> congr!)
    ?_ hSr hSc'
  intro s hs
  obtain ⟨hx,hu,hH⟩:=hS s hs
  have ha:markedCoverSpokeAllowed X Z σ s.1 s.2:=Or.inl ⟨hx,hu⟩
  refine ⟨hx,hu,?_⟩
  rcases hH with h|h
  · exact Or.inl ⟨h,ha⟩
  · exact Or.inr ⟨h,ha⟩
end Oberwolfach
