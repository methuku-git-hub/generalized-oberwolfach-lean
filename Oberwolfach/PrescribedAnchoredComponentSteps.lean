module

public import Oberwolfach.PrescribedOneEndedPathRealization
public import Oberwolfach.PrescribedTwoEndedPathRealization
public import Oberwolfach.PrescribedPinnedCycleRealization
public import Oberwolfach.PrescribedPathFromThrough
public import Oberwolfach.PrescribedMappedPhysicalStep

@[expose] public section
/-! Complete a component with one or two previously assigned boundaries,
updating its exact physical edges while protecting all other resources. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {X V I:Type} [Fintype X] [Fintype V] [DecidableEq X] [DecidableEq V] [DecidableEq I]

theorem prescribed_one_ended_component_step
    (as:List X) (ha:as.Nodup) (A:Finset X) (f:X→V)
    (hinj:Set.InjOn f A) (hsource:∀ u∈as,u∉A) (a:X) (haA:a∈A)
    (S L:Finset V) (β:ℝ) (D:V→V→Prop) (hext:IsExtendingList D L β)
    (F J:SimpleGraph V) (M:ℝ) (hM:0≤M) (hdeg:∀ v,(F.degree v:ℝ)≤M) (forward:Bool)
    (hbudget:((A.image f∪S).card:ℝ)+as.length+1+M<β*Fintype.card V)
    (E:I→Finset (Sym2 V)) (k:I) (hpair:PairwisePhysicalDisjoint E)
    (hcover:∀ j,E j⊆F.edgeFinset) (hJ:J.edgeFinset⊆F.edgeFinset):
    ∃ g:X→V,Set.InjOn g (↑(A∪as.toFinset):Set X) ∧ (∀ u∈A,g u=f u) ∧
      (∀ u∈as,g u∈L ∧ g u∉S) ∧ DirectedPathFrom D F forward (g a) (as.map g) ∧
      (let added:=(prescribedOneSidedPhysicalEdges a as).image (Sym2.map g);
       PairwisePhysicalDisjoint (Function.update E k (E k∪added)) ∧ Disjoint added J.edgeFinset) := by
  obtain ⟨g,hg,hpres,hlist,hpath⟩:=prescribed_one_ended_path_realization as ha A f hinj hsource a haA S L β D hext F M hM hdeg forward hbudget
  exact ⟨g,hg,hpres,hlist,hpath,prescribed_one_ended_mapped_physical_step g D F J forward a as hpath E k hpair hcover hJ⟩

theorem prescribed_two_ended_component_step
    (as:List X) (ha:as.Nodup) (hne:1≤as.length) (A:Finset X) (f:X→V)
    (hinj:Set.InjOn f A) (hsource:∀ u∈as,u∉A) (a b:X) (haA:a∈A) (hbA:b∈A) (hab:a≠b)
    (S L:Finset V) (β:ℝ) (D:V→V→Prop) (hext:IsExtendingList D L β)
    (F J:SimpleGraph V) (M:ℝ) (hM:0≤M) (hdeg:∀ v,(F.degree v:ℝ)≤M)
    (hbudget:((A.image f∪S).card:ℝ)+as.length+2+2*M<β*Fintype.card V)
    (E:I→Finset (Sym2 V)) (k:I) (hpair:PairwisePhysicalDisjoint E)
    (hcover:∀ j,E j⊆F.edgeFinset) (hJ:J.edgeFinset⊆F.edgeFinset):
    ∃ g:X→V,Set.InjOn g (↑(A∪as.toFinset):Set X) ∧ (∀ u∈A,g u=f u) ∧
      (∀ u∈as,g u∈L ∧ g u∉S) ∧ DirectedPathThrough D F (g a) (g b) (as.map g) ∧
      (let added:=(prescribedPathPhysicalEdges a b as).image (Sym2.map g);
       PairwisePhysicalDisjoint (Function.update E k (E k∪added)) ∧ Disjoint added J.edgeFinset) := by
  obtain ⟨g,hg,hpres,hlist,hpath⟩:=prescribed_two_ended_path_realization as ha hne A f hinj hsource a b haA hbA hab S L β D hext F M hM hdeg hbudget
  have ht:=prescribed_path_from_to_through D F (g b) (as.map g) (g a) hpath
  exact ⟨g,hg,hpres,hlist,ht,prescribed_two_ended_mapped_physical_step g D F J a b as ht E k hpair hcover hJ⟩

theorem prescribed_pinned_cycle_component_step
    (as:List X) (ha:as.Nodup) (hlen:2≤as.length) (A:Finset X) (f:X→V)
    (hinj:Set.InjOn f A) (hsource:∀ u∈as,u∉A) (a:X) (haA:a∈A)
    (S L:Finset V) (β:ℝ) (D:V→V→Prop) (hext:IsExtendingList D L β)
    (F J:SimpleGraph V) (M:ℝ) (hM:0≤M) (hdeg:∀ v,(F.degree v:ℝ)≤M)
    (hbudget:((A.image f∪S).card:ℝ)+(as.length+1:ℕ)+2+2*M<β*Fintype.card V)
    (E:I→Finset (Sym2 V)) (k:I) (hpair:PairwisePhysicalDisjoint E)
    (hcover:∀ j,E j⊆F.edgeFinset) (hJ:J.edgeFinset⊆F.edgeFinset):
    ∃ g:X→V,Set.InjOn g (↑(A∪as.toFinset):Set X) ∧ (∀ u∈A,g u=f u) ∧
      (∀ u∈as,g u∈L ∧ g u∉S) ∧ DirectedPathThrough D F (g a) (g a) (as.map g) ∧
      (let added:=(prescribedCyclePhysicalEdges (a::as)).image (Sym2.map g);
       PairwisePhysicalDisjoint (Function.update E k (E k∪added)) ∧ Disjoint added J.edgeFinset) := by
  obtain ⟨g,hg,hpres,hlist,hpath⟩:=prescribed_pinned_cycle_realization as ha hlen A f hinj hsource a haA S L β D hext F M hM hdeg hbudget
  have hc:DirectedCycleThrough D F ((a::as).map g):=hpath
  exact ⟨g,hg,hpres,hlist,hpath,prescribed_cycle_mapped_physical_step g D F J (a::as) hc E k hpair hcover hJ⟩
end Oberwolfach
