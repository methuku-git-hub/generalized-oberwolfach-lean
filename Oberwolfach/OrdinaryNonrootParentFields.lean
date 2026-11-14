module

public import Oberwolfach.OrdinaryEditedParentFields
public import Oberwolfach.OrdinaryNonrootParentCuts
public import Oberwolfach.OrdinaryNonrootSpokeDegree
public import Oberwolfach.OrdinaryNonrootCountsLower
public import Oberwolfach.OrdinaryNonrootWeightLoads
public import Oberwolfach.BipartiteLargeCutInstances

@[expose] public section
/-! Restrict the original parent fields to adaptive nonroot domains.
All numerical losses are explicit and no new sample is introduced. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_nonroot_parent_fields
    (r:ℕ) (hr:3≤r) (k:ℕ) (α β βfree b bfree B Bfree h δ δfree ε εfree κ:ℝ)
    (P Q F:SimpleGraph V) (H:V→U→Prop) (T:Finset V) (W:Finset U)
    (d:OrdinaryEditedParentFields r hr k α β b B h δ ε P Q F H)
    (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V) (hk:4≤k)
    (hA:0<Fintype.card ↥(Finset.univ\T)) (hBdom:0<Fintype.card ↥(Finset.univ\W))
    (hκ:0<κ) (hh:0≤h) (hb:0≤b) (hB:0≤B)
    (hAsize:κ*Fintype.card V≤(Fintype.card ↥(Finset.univ\T):ℝ))
    (hBsize:κ*Fintype.card U≤(Fintype.card ↥(Finset.univ\W):ℝ))
    (hcutoff:1-2*δ≤κ*(1-2*δfree))
    (hdegree:βfree*Fintype.card ↥(Finset.univ\T)+(W.card:ℝ)≤β*Fintype.card V)
    (hiso:βfree*(Fintype.card ↥(Finset.univ\T):ℝ)^(k-1)+
      ((T.card:ℝ)+W.card)*(Fintype.card V:ℝ)^(k-2)≤β*(Fintype.card V:ℝ)^(k-1))
    (htransfer:βfree*(Fintype.card ↥(Finset.univ\T):ℝ)^(r^2)+
      (T.card:ℝ)*(r:ℝ)^2*(Fintype.card V:ℝ)^(r^2-1)≤β*(Fintype.card V:ℝ)^(r^2))
    (hweightlo:bfree/(Fintype.card ↥(Finset.univ\T):ℝ)^(r-1)≤b/(Fintype.card V:ℝ)^(r-1))
    (hweighthi:B/(Fintype.card V:ℝ)^(r-1)≤Bfree/(Fintype.card ↥(Finset.univ\T):ℝ)^(r-1))
    (herror:ε+((T.card:ℝ)+W.card)*((r:ℝ)^4*B/Fintype.card V)≤εfree):
    let A:=Finset.univ\T;let C:=Finset.univ\W;
    Nonempty (OrdinaryEditedParentFields r hr k α βfree bfree Bfree h δfree εfree
      (P.induce (A:Set V)) (Q.induce (A:Set V)) (F.induce (A:Set V))
      (fun (v:A) (u:C)=>H v.val u.val)):=by
  intro A C
  have hcuts:=ordinary_nonroot_parent_cuts d.orientation H T W κ δ δfree h hκ hh hA hBdom hAsize hBsize hcutoff d.rim_cuts d.spoke_cuts
  have hdeg:=ordinary_nonroot_spoke_degree H T W β βfree d.spoke_degree hdegree
  have hiso':=ordinary_nonroot_isolator_lower P Q F H k (max (1/2) (cycleThreshold r)) (α/4) β βfree
    T W (by omega) hn hu d.isolators hiso
  have hparentT:∀v u u',H v u→H v u'→u≠u'→β*(Fintype.card V:ℝ)^(r^2)≤
      (Fintype.card (OrdinaryTransferConfiguration hr Q F H v u u'):ℝ):=by
    intro v u u' hu hu' hne
    exact d.transfers v ⟨u,hu⟩ ⟨u',hu'⟩ hne
  have ht:=ordinary_nonroot_transfer_lower Q F H r hr β βfree T W hparentT htransfer
  have hw:∀D,0≤d.weight D ∧ d.weight D≤B/(Fintype.card V:ℝ)^(r-1):=by
    intro D
    exact ⟨(div_nonneg hb (by positivity)).trans (d.weight_bounds D).1,(d.weight_bounds D).2⟩
  have hloads:=ordinary_nonroot_weight_loads Q F H r (by omega) hn hu d.weight B ε hB hw d.rim_load d.spoke_load T W
  let w':=ordinaryInducedWheelWeight Q F H A C r d.weight
  refine ⟨⟨(fun x y=>d.orientation x.val y.val),?_,?_,?_,?_,?_,?_,w',?_,?_,?_⟩⟩
  · intro x y
    exact d.orientation_graph x.val y.val
  · exact bipartite_large_cut_reinstance hcuts.1
  · exact bipartite_large_cut_reinstance hcuts.2
  · intro v
    convert hdeg v using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  · intro x y hxy
    convert hiso' x y hxy using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  · intro v i j hne
    convert ht v i.val j.val i.property j.property hne using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  · intro D
    let E : {E:OrdinaryWheel Q F H r // (ordinaryWheelRim E).support⊆(A:Set V) ∧ ordinaryWheelHub E∈C} :=
      (ordinaryInducedWheelEquiv Q F H A C r).symm D
    change bfree/(Fintype.card A:ℝ)^(r-1)≤d.weight E.val ∧ d.weight E.val≤Bfree/(Fintype.card A:ℝ)^(r-1)
    exact ⟨hweightlo.trans (d.weight_bounds E.val).1,(d.weight_bounds E.val).2.trans hweighthi⟩
  · intro x y hxy
    apply le_trans ?_ herror
    convert hloads.1 x y hxy using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro v u huv
    apply le_trans ?_ herror
    convert hloads.2 v u huv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
