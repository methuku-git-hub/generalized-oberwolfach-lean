module

public import Oberwolfach.OrdinaryPrescribedBoundarySpokeMatchingShape

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_prescribed_boundary_spoke_matching_named
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    {X J:U→Type} [∀w,Fintype (X w)] [∀w,DecidableEq (X w)] [∀w,DecidableEq (J w)]
    (π:Equiv.Perm (Fin n)) (d m c:ℕ) (hd:1≤d)
    (Rim:(Fin n×Fin n)⊕(Fin n×Fin n)→Prop)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t):
    OrdinaryPrescribedBoundarySpokeMatchingShape (K:=K) (X:=X) (J:=J) π d m c hd Rim raw t Jret :=by
  unfold OrdinaryPrescribedBoundarySpokeMatchingShape
  intro σ H RM state RR φ L W hW F data ext ψ hc hdd hs₂ hsupp hmarker hT Bbound Rbound Q Row hrows hboundary v
  let root:=fun w i=>retainedAndRawIntervalRoot π d σ false true t Jret w i
  let colour:=fun w (i:retainedMarkedIndex π d σ false t Jret w ⊕
      {a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true})=>match i with | Sum.inl _=>false | Sum.inr _=>true
  let Covered:=fun x=>Finset.univ.filter (fun w=>∃Z∈Finset.univ.image (W w),Sum.inr (x,w)∈markedWheelPhysicalResources Z)
  let Defect:=fun x w=>H true x w ∧ ¬∃Z∈Finset.univ.image (W w),Sum.inr (x,w)∈markedWheelPhysicalResources Z
  have hroot:∀w i,i∈(data w).s₁∪(data w).s₂→ rawIntervalColouredStart π d (fun e=>σ (w,e)) (root w i) (colour w i):=by
    intro w i hi
    cases i with
    | inl b=>exact b.property.1
    | inr b=>exact b.property
  have hgeom:∀w i,i∈(data w).s₁∪(data w).s₂→∀j≤d,
      ((data w).P i |>.getVert (2+(data w).c*j))∈(data w).prescribed→
      ψ w ((data w).P i |>.getVert (2+(data w).c*j))=(π^j) (root w i):=by
    intro w
    exact actual_prescribed_marker_image_geometry_polymorphic (data w) c d (hc w) (hdd w) (ext w) (ψ w) π (root w) (hsupp w) (hmarker w)
  have hfirst:∀w i,i∈(data w).s₁∪(data w).s₂→((data w).P i |>.getVert 2)∈(data w).prescribed→ψ w ((data w).P i |>.getVert 2)=root w i:=by
    intro w i hi hp
    simpa only [Nat.mul_zero,Nat.add_zero,pow_zero,Equiv.Perm.one_apply] using hgeom w i hi 0 (by omega) (by simpa using hp)
  have hlast:∀w i,i∈(data w).s₁∪(data w).s₂→((data w).P i |>.getVert (2+(data w).c*(data w).d))∈(data w).prescribed→ψ w ((data w).P i |>.getVert (2+(data w).c*(data w).d))=(π^d) (root w i):=by
    intro w i hi hp
    simpa only [hdd w] using hgeom w i hi d (le_refl d) (by simpa only [hdd w] using hp)
  have hmiss:∀w i,i∈(data w).s₂→∀j<d,j∉(data w).T i→Defect ((π^j) (root w i)) w:=by
    intro w i hi j hj hnot
    exact ordinary_missing_position_uncovered_spoke π d m (3*d) hd raw t Jret _ _ _ _
      (fun w=>Finset.univ.image (W w)) F data hs₂ hT w i hi j hj hnot
  have hvertex:=ordinary_uncovered_marked_spokes_le_vertex_matching_row (K:=K) π d m Rim H
    (raw_marked_pair_spoke_exclusive π d raw) L W hW
  have hdef:∀x,((Finset.univ.filter (fun w=>Defect x w)).card:ℝ)≤Rbound:=by
    intro x
    have hsub:Finset.univ.filter (fun w=>Defect x w)⊆(Finset.univ.filter (fun w=>H true x w))\Covered x:=by
      intro w hw
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Defect] at hw
      apply Finset.mem_sdiff.mpr
      constructor
      · simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hw.1
      · simpa only [Covered,Finset.mem_filter,Finset.mem_univ,true_and] using hw.2
    have hcard:((Finset.univ.filter (fun w=>Defect x w)).card:ℝ)≤(((Finset.univ.filter (fun w=>H true x w))\Covered x).card:ℝ):=by
      exact_mod_cast Finset.card_le_card hsub
    have hv:=hvertex x
    have hv':(((Finset.univ.filter (fun w=>H true x w))\Covered x).card:ℝ)≤((Row x\L.biUnion Q).card:ℝ):=by
      exact_mod_cast hv
    exact hcard.trans (hv'.trans (hrows x))
  have hh:=actual_prescribed_multiplicity_from_boundary_spoke_defects_dependent π d σ F data ψ root colour Finset.univ hroot hfirst hlast
    Defect hdd (by intro w i hi;exact hgeom w i (Finset.mem_union_right _ hi)) hmiss v Bbound Rbound Rbound
    (hboundary v) (by convert hdef v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by convert hdef (π.symm v) using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  linarith only [hh]
end Oberwolfach
