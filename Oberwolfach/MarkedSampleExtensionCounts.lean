module

public import Oberwolfach.MarkedEventLocalExtensions
public import Oberwolfach.MarkedBoundaryCountsFromLocalExtensions
public import Oberwolfach.MarkedSampleOccurrenceMatrix
public import Oberwolfach.MarkedFiniteRemainder

@[expose] public section

/-! Actual sampled arc identifiers, rather than potential arcs, supply the
separation used by the two-vertex hub extension. Both extension families
retain the original fixed row and index domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_sample_arc_present_pair (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (j:Bool) (x y:V):
    markedArcPresent
      (fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
      (fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2) j x y ↔
      rawMarkedPairRims P π d σ (if j then Sum.inr (x,y) else Sum.inl (x,y)):=by
  cases j <;> simp only [markedArcPresent,Bool.false_eq_true,ite_false,ite_true,rawMarkedPairRims,
    Sum.elim_inl,Sum.elim_inr,markedSampleArc_indicator_iff]

theorem marked_sample_arc_separated (P:SimpleGraph V) (π:Equiv.Perm V) (b:ℕ)
    (σ:Sym2 V→Option (Bool×Bool))
    (a:MarkedSampleArc P π b σ false⊕MarkedSampleArc P π b σ true):
    ¬PermutationClose π b (Sum.elim (fun e=>e.val.1) (fun e=>e.val.1) a)
      (Sum.elim (fun e=>e.val.2) (fun e=>e.val.2) a):=by
  cases a with
  | inl a=>exact ((markedPhysicalRim_eq_one_iff P π b σ false _ _).mp a.property).1
  | inr a=>exact ((markedPhysicalRim_eq_one_iff P π b σ true _ _).mp a.property).1

theorem marked_common_two_vertex_hubs (π:Equiv.Perm V) (b h:ℕ) (hh:2≤h)
    (B:Finset U) (H:Bool→V→U→Prop) (a:ℝ)
    (hcommon:∀ X Y:Finset V,Disjoint X Y→(X∪Y).card≤h→
      ((X∪Y):Set V).Pairwise (fun x y=>¬PermutationClose π b x y)→
      a≤((common (common B X (fun v=>Finset.univ.filter (H false v))) Y
        (fun v=>Finset.univ.filter (H true v))).card:ℝ))
    (j:Bool) (x y:V) (hxy:¬PermutationClose π b x y):
    a≤((B.filter (fun u=>H false x u∧(if j then H true y u else H false y u))).card:ℝ):=by
  have hne:x≠y:=fun he=>hxy (Or.inl he)
  have hsep:({x,y}:Set V).Pairwise (fun v w=>¬PermutationClose π b v w):=by
    intro v hv w hw hvw
    rcases hv with rfl|rfl <;> rcases hw with rfl|rfl
    · exact (hvw rfl).elim
    · exact hxy
    · exact fun h=>hxy ((permutationClose_symm π b _ _).mp h)
    · exact (hvw rfl).elim
  cases j
  · have he:=hcommon {x,y} ∅ (by simp) (by simpa using (Finset.card_le_two.trans hh))
      (by simpa using hsep)
    simpa [common,Finset.filter_filter] using he
  · have he:=hcommon {x} {y} (by simpa using hne)
      (by simpa using (Finset.card_le_two.trans hh)) (by simpa [Set.pair_comm] using hsep)
    simpa only [common,Finset.filter_filter,Finset.mem_singleton,forall_eq,Finset.mem_filter,
      Finset.mem_univ,true_and,ite_true] using he

theorem marked_sample_extension_counts
    (P:SimpleGraph V) (π:Equiv.Perm V) (d h:ℕ) (hh:2≤h)
    (A:Finset V) (B:Finset U) (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (a b:ℝ)
    (hstep:∀ j x u,a≤((markedOneExtensionSet (rawMarkedPairRims P π d σ) H A j x u).card:ℝ))
    (hjoin:∀ j x y u,x≠(if j then π y else y)→
      a≤((markedTwoExtensionSet (rawMarkedPairRims P π d σ) H A j x y u).card:ℝ))
    (hcommon:∀ X Y:Finset V,Disjoint X Y→(X∪Y).card≤h→
      ((X∪Y):Set V).Pairwise (fun x y=>¬PermutationClose π (3*d) x y)→
      b≤((common (common B X (fun v=>Finset.univ.filter (H false v))) Y
        (fun v=>Finset.univ.filter (H true v))).card:ℝ)):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1; let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1; let khead:=fun e:K=>e.val.2;
    MarkedBoundaryExtensionCounts tail head ktail khead (H false) (H true) A a ∧
    (∀ j x y u,x≠(if j then π y else y)→a≤((A.filter (fun z=>
      markedArcPresent tail head ktail khead false x z∧
      markedArcPresent tail head ktail khead j z y∧H false z u)).card:ℝ)) ∧
    (∀ e:E⊕K,¬PermutationClose π (3*d) (Sum.elim tail ktail e) (Sum.elim head khead e)) ∧
    (∀ e:E⊕K,b≤((B.filter (fun u=>H false (Sum.elim tail ktail e) u∧
      (if markedArcType e then H true (Sum.elim head khead e) u else
        H false (Sum.elim head khead e) u))).card:ℝ)):=by
  dsimp only
  refine ⟨marked_boundary_counts_from_local_extensions (rawMarkedPairRims P π d σ) H A a
    hstep (fun x y u hxy=>hjoin false x y u hxy),?_,?_,?_⟩
  · intro j x y u hxy
    convert hjoin j x y u hxy using 1
    congr 2
    ext z
    simp only [Finset.mem_filter,markedTwoExtensionSet,marked_sample_arc_present_pair,
      Bool.false_eq_true,ite_false]
  · exact marked_sample_arc_separated P π (3*d) _
  · intro e
    exact marked_common_two_vertex_hubs π (3*d) h hh B H b hcommon (markedArcType e) _ _
      (marked_sample_arc_separated P π (3*d) _ e)

end Oberwolfach
