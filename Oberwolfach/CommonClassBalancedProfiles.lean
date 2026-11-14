module

public import Oberwolfach.CommonClassBalanceBounds
public import Oberwolfach.BalancedClassTolerance
public import Oberwolfach.ClassWeightStability
public import Oberwolfach.TypedClassCountStability
public import Oberwolfach.ClassMarkedAbsorberCounts
public import Oberwolfach.ClassCountMargins

@[expose] public section

/-! Common-class balancing with the original weights and actual paired
absorber records. Tolerances precede the forbidden-set size, permutation,
separation distance, host, classes, and roots. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

 theorem common_class_balanced_profiles (m:ℕ) (hm:3<m+1)
    (q₀ β blo bhi η:ℝ) (hq₀:0<q₀) (hβ:0<β) (hblo:0<blo) (hbhi:0<bhi) (hη:0<η):
    ∃ ε:ℝ,0<ε∧∀ f:ℝ,0≤f→∃ N:ℕ,1≤N∧
    ∀ (V E K:Type) [Fintype V] [DecidableEq V],N≤Fintype.card V→
    ∀ (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V) (b:ℕ)
      (A₀ B₀ I ZK ZO:Finset V) (q:ℝ),q₀≤q→
    Disjoint A₀ (B₀∪ZO)→ZK⊆A₀→Disjoint (ZK∪ZO) I→
    Disjoint ZK (ZO.image π.symm)→ZO.card=m*ZK.card→
    |(A₀.card:ℝ)-q*Fintype.card V|≤ε*Fintype.card V→
    |(B₀.card:ℝ)-m*q*Fintype.card V|≤ε*Fintype.card V→
    (I.card:ℝ)≤ε*Fintype.card V→
    ((B₀∩A₀.image π).card:ℝ)≤ε*Fintype.card V→(ZO.card:ℝ)≤f→
    β*(Fintype.card V:ℝ)^(m+1)≤Fintype.card (ClassMarkedCycle tail head ktail khead m π b A₀ B₀)→
    (∀ j:Bool,∀ v v':V,v≠v'→
      β*(Fintype.card V:ℝ)^m≤Fintype.card (RootFirstCommonMarkedPath tail head ktail khead m π b
        (fun x (_:Unit)=>x∈B₀) (fun x (_:Unit)=>x∈A₀) j v v' () ()))→
    ∀ w:MarkedCycleTuple tail head ktail khead m π b→ℝ,
    (∀ C,blo/(Fintype.card V:ℝ)^m≤w C∧w C≤bhi/(Fintype.card V:ℝ)^m)→
    (∀ j:Bool,∀ v:V,|1-resourceRootOmittedLoad typedMarkedCycleVertices w
      (fun x=>x∈typedClassSet A₀ B₀) (j,v)|≤ε)→
    ∃ A B:Finset V,ZK⊆A∧ZO⊆B∧A⊆A₀∧B⊆B₀∪ZO∧Disjoint A B∧
      Disjoint (A∪B) I∧Disjoint B (A.image π)∧B.card=m*A.card∧
      q₀/2*(Fintype.card V:ℝ)≤A.card∧
      (∀ v∈A∪B,|1-hypergraphWeightedDegree classMarkedCycleVertices
        (fun C:ClassMarkedCycle tail head ktail khead m π b A B=>w (classMarkedCycleAsMarked C)) v|≤η)∧
      (∀ X:Finset V,X⊆A∪B→(X∩A).card=1→(X∩B).card=m→
        (β/4)^(m+2)*(Fintype.card V:ℝ)^((m+1)*(m+1))≤
          Fintype.card (LabelledAbsorberFamily (classMarkedCycleVertices (tail:=tail) (head:=head)
            (ktail:=ktail) (khead:=khead) (m:=m) (π:=π) (b:=b) (A:=A) (B:=B))
            (fun (_:Unit)=>pairedAbsorberTemplate (m+1)) X)):=by
  let K₀:ℝ:=((m+1)^(m+1):ℕ)*3^(m-1)*bhi
  have hK₀:0≤K₀:=by dsimp [K₀];positivity
  obtain ⟨ε,δ,hε,hδ,hsize,herr,hcount,horder⟩:=balanced_class_tolerances m q₀ β η K₀ hq₀ hβ hη hK₀
  obtain ⟨Nabs,habs⟩:=class_marked_absorber_counts m hm (β/2) (by positivity)
  refine ⟨ε,hε,?_⟩
  intro f hf
  obtain ⟨Nloss,hNloss,hloss⟩:=horder f hf
  refine ⟨max Nabs Nloss,hNloss.trans (le_max_right _ _),?_⟩
  intro V E K _ _ hn tail head ktail khead π b A₀ B₀ I ZK ZO q hq hAB hZA hZI hsep hZ hAc hBc hIc hOc hZc hbase hpath w hw hroot
  have hnabs:Nabs≤Fintype.card V:=(le_max_left _ _).trans hn
  have hnloss:Nloss≤Fintype.card V:=(le_max_right _ _).trans hn
  have hn1:1≤Fintype.card V:=hNloss.trans hnloss
  have hn0:(0:ℝ)<Fintype.card V:=by exact_mod_cast (show 0<Fintype.card V by omega)
  obtain ⟨A,B,hZKA,hZOB,hAA,hBB,hdis,hI,hπ,hcard,hL,hAsize⟩:=
    common_class_balance_bounds π m (by omega) A₀ B₀ I ZK ZO hAB hZA hZI hsep hZ
      (Fintype.card V) q ε f (by positivity) hε.le hAc hBc hIc hOc hZc
  let L:ℝ:=(changed A₀ A).card+(changed B₀ B).card
  have hLδ:L≤δ*Fintype.card V:=hL.trans (hloss _ hnloss)
  have hAq:q₀/2*(Fintype.card V:ℝ)≤A.card:=by
    have hq':q₀*(Fintype.card V:ℝ)≤q*Fintype.card V:=mul_le_mul_of_nonneg_right hq hn0.le
    have hs:=(mul_le_mul_of_nonneg_right hsize hn0.le)
    nlinarith only [hAsize,hLδ,hq',hs]
  have hw0:∀ C,0≤w C∧w C≤bhi/(Fintype.card V:ℝ)^m:=fun C=>
    ⟨(by positivity:0≤blo/(Fintype.card V:ℝ)^m).trans (hw C).1,(hw C).2⟩
  have hweights:∀ v∈A∪B,|1-hypergraphWeightedDegree classMarkedCycleVertices
      (fun C:ClassMarkedCycle tail head ktail khead m π b A B=>w (classMarkedCycleAsMarked C)) v|≤η:=by
    intro v hv
    have hh:=class_weight_degree_stability (by omega) hn1 w bhi ε hbhi.le hw0 A₀ B₀ A B hdis hroot v hv
    have hsmall:K₀*L/(Fintype.card V:ℝ)≤K₀*δ:=by
      apply (div_le_iff₀ hn0).mpr
      nlinarith only [mul_le_mul_of_nonneg_left hLδ hK₀]
    exact hh.trans (by change ε+K₀*L/(Fintype.card V:ℝ)≤η;linarith)
  have hbase':β/2*(Fintype.card V:ℝ)^(m+1)≤
      Fintype.card (ClassMarkedCycle tail head ktail khead m π b A B):=by
    have hh:=class_marked_cycle_count_change tail head ktail khead m π b A₀ B₀ A B
    exact class_count_margin (m+1) (by omega) (Fintype.card V) β (m+1) δ L _ _
      hn0.le (by positivity) hLδ hcount hbase (by simpa only [Nat.add_sub_cancel] using hh)
  have hpath':∀ j:Bool,∀ v v':V,v≠v'→
      β/2*(Fintype.card V:ℝ)^m≤Fintype.card (RootFirstCommonMarkedPath tail head ktail khead m π b
        (fun x (_:Unit)=>x∈B) (fun x (_:Unit)=>x∈A) j v v' () ()):=by
    intro j v v' hne
    have hh:=class_marked_path_count_change tail head ktail khead m π b A₀ B₀ A B j v v'
    have hmargin:(m:ℝ)*δ≤β/2:=by nlinarith only [hcount,hδ.le]
    exact class_count_margin m (by omega) (Fintype.card V) β m δ L _ _
      hn0.le (by positivity) hLδ hmargin (hpath j v v' hne) hh
  refine ⟨A,B,hZKA,hZOB,hAA,hBB,hdis,hI,hπ,hcard,hAq,hweights,?_⟩
  intro X hX hXA hXB
  have hh:=habs V E K hnabs tail head ktail khead π b A B hdis hbase'
    (by intro j v v' hne _ _;simpa only [Fintype.card_eq_nat_card] using hpath' j v v' hne) X hX hXA hXB
  have he:(β/2)/2=β/4:=by ring
  simpa only [he] using hh

end Oberwolfach
