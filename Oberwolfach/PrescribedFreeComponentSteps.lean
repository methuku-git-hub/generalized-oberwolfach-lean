module

public import Oberwolfach.PrescribedFreePathStrong
public import Oberwolfach.PrescribedFreePathPhysicalEdges
public import Oberwolfach.PrescribedFreeCycleRealization
public import Oberwolfach.PrescribedMappedPhysicalStep

@[expose] public section
/-! Complete one component step: extend the partial injection and update the
actual physical edges while protecting other factors and the reserved graph. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {X V I:Type} [Fintype X] [Fintype V] [DecidableEq X] [DecidableEq V] [DecidableEq I]

theorem prescribed_free_path_component_step
    (as:List X) (ha:as.Nodup) (hne:1≤as.length) (A:Finset X) (f:X→V)
    (hinj:Set.InjOn f A) (hsource:∀ u∈as,u∉A)
    (S L:Finset V) (β:ℝ) (D:V→V→Prop) (hext:IsExtendingList D L β)
    (F J:SimpleGraph V) (M:ℝ) (hM:0≤M) (hdeg:∀ v,(F.degree v:ℝ)≤M)
    (hbudget:((A.image f∪S).card:ℝ)+as.length+2+M<β*Fintype.card V)
    (E:I→Finset (Sym2 V)) (k:I) (hpair:PairwisePhysicalDisjoint E)
    (hcover:∀ j,E j⊆F.edgeFinset) (hJ:J.edgeFinset⊆F.edgeFinset):
    ∃ g:X→V,Set.InjOn g (↑(A∪as.toFinset):Set X) ∧ (∀ u∈A,g u=f u) ∧
      (∀ u∈as,g u∈L ∧ g u∉S) ∧ DirectedNonemptyPath D F true (as.map g) ∧
      (let added:=(prescribedFreePathPhysicalEdges as).image (Sym2.map g);
       PairwisePhysicalDisjoint (Function.update E k (E k∪added)) ∧ Disjoint added J.edgeFinset) := by
  obtain ⟨g,hg,hpres,hlist,hpath⟩:=prescribed_free_path_realization_strong as ha hne A f hinj hsource S L β D hext F M hM hdeg hbudget
  exact ⟨g,hg,hpres,hlist,hpath,prescribed_free_path_mapped_physical_step g D F J as hpath E k hpair hcover hJ⟩

theorem prescribed_free_cycle_component_step
    (as:List X) (ha:as.Nodup) (hlen:3≤as.length) (A:Finset X) (f:X→V)
    (hinj:Set.InjOn f A) (hsource:∀ u∈as,u∉A)
    (S L:Finset V) (β:ℝ) (D:V→V→Prop) (hext:IsExtendingList D L β)
    (F J:SimpleGraph V) (M:ℝ) (hM:0≤M) (hdeg:∀ v,(F.degree v:ℝ)≤M)
    (hbudget:((A.image f∪S).card:ℝ)+as.length+2+2*M<β*Fintype.card V)
    (E:I→Finset (Sym2 V)) (k:I) (hpair:PairwisePhysicalDisjoint E)
    (hcover:∀ j,E j⊆F.edgeFinset) (hJ:J.edgeFinset⊆F.edgeFinset):
    ∃ g:X→V,Set.InjOn g (↑(A∪as.toFinset):Set X) ∧ (∀ u∈A,g u=f u) ∧
      (∀ u∈as,g u∈L ∧ g u∉S) ∧ DirectedCycleThrough D F (as.map g) ∧
      (let added:=(prescribedCyclePhysicalEdges as).image (Sym2.map g);
       PairwisePhysicalDisjoint (Function.update E k (E k∪added)) ∧ Disjoint added J.edgeFinset) := by
  obtain ⟨g,hg,hpres,hlist,hcycle⟩:=prescribed_free_cycle_realization as ha hlen A f hinj hsource S L β D hext F M hM hdeg hbudget
  exact ⟨g,hg,hpres,hlist,hcycle,prescribed_cycle_mapped_physical_step g D F J as hcycle E k hpair hcover hJ⟩
end Oberwolfach
