module

public import Oberwolfach.MarkedSampleSeedWitness
public import Oberwolfach.MarkedSampleSeedPresentRootBounds
public import Oberwolfach.MarkedInducedSampleStates
public import Oberwolfach.TypedMarkedPotentialVertexDeletion

@[expose] public section

/-! Restrict the original normalized weights to a fixed invariant row
complement and a hub complement. Retained roots lose only the explicitly
bounded forbidden-vertex weight; the original normalization is retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_induced_sample_seed_witness
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (hm:3≤m) (hn:0<Fintype.card V)
    (hu:Fintype.card U≤Fintype.card V) (D τ A B p k s₀ pstar η:ℝ)
    (hDlo:(Fintype.card V:ℝ)/2≤D) (hDhi:D≤2*Fintype.card V)
    (hpstar:0<pstar) (hp:pstar≤p) (hk:pstar≤k) (hs:pstar≤s₀)
    (hp1:p≤1) (hk1:k≤1) (hs1:s₀≤1) (hA:0≤A) (hB:0≤B) (hη:0≤η)
    (weight:(Fin (m+1)→V)→ℝ) (hw:SuccessorSequenceWeightConditions P π (3*d) D τ A B weight)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color)
    (hq:∀ u,0<q u g) (hS:∀ u,0<s u j)
    (hload:
      let seed:=fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
        (fun (_:V) (_:U)=>True) (fun _ _=>True)=>weight W.1.val/(D*p^m*k*s₀^m)
      ∀ root,rawMarkedWheelMarginal P π d p k q s g j root≠0→
        |typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) H root-1|≤η)
    (T:Finset V) (Z:Finset U) (hT:∀ x,π x∈T↔x∈T):
    let X:=Finset.univ\T
    let P₀:=spanningRestriction P X
    let H':=fun j v u=>H j v u∧v∉T∧u∉Z
    let η':=η+((T.card:ℝ)+Z.card)*((m:ℝ)+1)^3*(2*B/pstar^(2*m+1))/Fintype.card V
    let E:=MarkedSampleArc P₀ π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P₀ π (3*d) (fun e=>σ (Sum.inl e)) true
    let ψ:=fun W:MarkedWheel (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) m π (3*d) (H' false) (H' true)=>weight W.1.val/(D*p^m*k*s₀^m)
    (∀ e,|markedWheelRimLoad ψ e-1|≤η')∧
    (∀ j v u,|markedSpokeResidual ψ j v u|≤η')∧
    (∀ W,(A/2)/(Fintype.card V:ℝ)^m≤ψ W∧ψ W≤(2*B/pstar^(2*m+1))/(Fintype.card V:ℝ)^m):=by
  intro X P₀ H' η' E K ψ
  let seed:=fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
    (fun (_:V) (_:U)=>True) (fun _ _=>True)=>weight W.1.val/(D*p^m*k*s₀^m)
  have hseed:=fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
    (fun (_:V) (_:U)=>True) (fun _ _=>True)=>successor_seed_nonneg_upper hw (by omega) hn hDlo hDhi
      p k s₀ pstar hpstar hp hk hs hp1 hk1 hs1 hB W.1.val
  have hX:∀ x,π x∈X↔x∈X:=by intro x;simp only [X,Finset.mem_sdiff,Finset.mem_univ,true_and,hT]
  have hR:rawMarkedPairRims P₀ π d σ=
      (fun a=>rawMarkedPairRims P π d σ a∧Sum.elim Prod.fst Prod.fst a∉T∧Sum.elim Prod.snd Prod.snd a∉T):=by
    rw [rawMarkedPairRims_spanningRestriction P π d X hX]
    funext a
    simp only [X,Finset.mem_sdiff,Finset.mem_univ,true_and]
  have hcost (root:((V×V)⊕(V×V))⊕(Bool×V×U))
      (hroot:Sum.elim (fun a=>Sum.elim Prod.fst Prod.fst a∉T∧Sum.elim Prod.snd Prod.snd a∉T)
        (fun s=>s.2.1∉T∧s.2.2∉Z) root)
      (hmarg:rawMarkedWheelMarginal P π d p k q s g j root≠0):
      |typedMarkedPotentialLoad seed (rawMarkedPairRims P₀ π d σ) H' root-1|≤η':=by
    have hc:=typedMarkedPotentialLoad_vertex_deletion (by omega) hn hu seed (2*B/pstar^(2*m+1))
      (by positivity) (fun W=>(hseed W).1) (fun W=>(hseed W).2)
      (rawMarkedPairRims P π d σ) H T Z root hroot
    rw [←hR] at hc
    have hh:=abs_sub_le (typedMarkedPotentialLoad seed (rawMarkedPairRims P₀ π d σ) H' root)
      (typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) H root) 1
    exact hh.trans ((add_le_add hc (hload root hmarg)).trans_eq (by dsimp [η'];ring))
  have heta:0≤η':=by dsimp [η'];positivity
  have hactual:=marked_sample_seed_present_root_bounds P₀ π d m D p k s₀ η' heta weight σ H'
  obtain ⟨hRload,hSload⟩:=hactual (by
    intro a
    apply hcost
    · cases a with
      | inl a=>
        have ha:=markedSampleArc_spanningRestriction_support P π (3*d) X hX _ false a
        simpa only [X,Sum.map_inl,Sum.elim_inl,Finset.mem_sdiff,Finset.mem_univ,true_and] using ha
      | inr a=>
        have ha:=markedSampleArc_spanningRestriction_support P π (3*d) X hX _ true a
        simpa only [X,Sum.map_inr,Sum.elim_inl,Sum.elim_inr,Finset.mem_sdiff,Finset.mem_univ,true_and] using ha
    · cases a with
      | inl a=>
        have hpres:=((markedPhysicalRim_spanningRestriction_iff P π (3*d) X hX _ false a.val.1 a.val.2).mp a.property).1
        have ha:=(markedPhysicalRim_eq_one_iff P π (3*d) _ false _ _).mp hpres
        have ha':¬PermutationClose π (3*d) a.val.1 a.val.2∧P.Adj a.val.1 a.val.2:=⟨ha.1,ha.2.1⟩
        simpa only [Sum.map_inl,rawMarkedWheelMarginal,if_pos ha'] using (hpstar.trans_le hp).ne'
      | inr a=>
        have hpres:=((markedPhysicalRim_spanningRestriction_iff P π (3*d) X hX _ true a.val.1 a.val.2).mp a.property).1
        have ha:=(markedPhysicalRim_eq_one_iff P π (3*d) _ true _ _).mp hpres
        have ha':¬PermutationClose π (3*d) a.val.1 a.val.2∧P.Adj a.val.1 (π a.val.2):=⟨ha.1,ha.2.1⟩
        simpa only [Sum.map_inr,rawMarkedWheelMarginal,if_pos ha'] using (hpstar.trans_le hk).ne') (by
    intro mark v u he
    apply hcost (Sum.inr (mark,v,u)) he.2
    cases mark <;> simp only [rawMarkedWheelMarginal,Bool.false_eq_true,ite_false,ite_true]
    · exact (hS u).ne'
    · exact (hq u).ne')
  refine ⟨hRload,hSload,?_⟩
  intro W
  have hvalid:SuccessorSequenceValid P π W.1.val:=by
    have hh:=marked_sample_cycle_valid P₀ π (3*d) m _ W.1
    intro i
    exact ((spanningRestriction_adj P X _ _).mp (hh i)).1
  exact ⟨successor_seed_positive_lower hw (by omega) hn hDlo hDhi p k s₀ pstar hpstar hp hk hs hp1 hk1 hs1 hA hB
    W.1.val hvalid W.1.property.1,
    (successor_seed_nonneg_upper hw (by omega) hn hDlo hDhi p k s₀ pstar hpstar hp hk hs hp1 hk1 hs1 hB W.1.val).2⟩

end Oberwolfach
