module

public import Oberwolfach.OrdinaryDeepCoverSeparateLoadEvent
public import Oberwolfach.OrdinaryDeepRemainderAvoidsInner
public import Oberwolfach.OrdinaryDeepUnionOuterDegree
public import Oberwolfach.OrdinaryDeepUnionNonrootDegree

@[expose] public section
/-! Recover the actual union of the prescribed and deep packings, retaining
    the physical outer-degree bounds for every ordinary wheel length. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 9000000
set_option synthInstance.maxSize 16384
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_deep_finite_cover_separate_load_nonroot_degree
    (m K:ℕ) (a aLoad ρ θ:ℝ) (P F Q:SimpleGraph V) (H:V→U→Prop) (J:Finset U)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (σ:RawWheelOutcome V U Γ Color)
    (hDeep:OrdinaryDeepCoverSeparateLoadEvent m K a aLoad ρ θ P F J π d j σ)
    (L:ℝ) (hQ:Q≤P\F) (hL:0≤L) (hLρ:L≤ρ*Fintype.card V) (hF:∀v,(F.degree v:ℝ)≤L)
    (hQR:∀v,((changed ((rawWheelGraph P σ).neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L)
    (hHr:∀v,((changed (Finset.univ.filter (rawWheelSpokes π d σ j v)) (Finset.univ.filter (H v))).card:ℝ)≤L)
    (hHc:∀u,((changed (Finset.univ.filter (fun v=>rawWheelSpokes π d σ j v u))
      (Finset.univ.filter (fun v=>H v u))).card:ℝ)≤L)
    (I:Finset V) (hI:(I.card:ℝ)≤a*Fintype.card V)
    (E:Finset (Sym2 V⊕(V×U))) (D₀:ℕ)
    (hE:E⊆ordinaryHostResources (spanningRestriction Q I) (fun v u=>H v u∧v∈I∧u∈J))
    (hFE:∀v w,Sum.inl s(v,w)∈E→¬F.Adj v w)
    (hDE:∀x,(E.filter (ordinaryResourceIncident x)).card≤D₀)
    (hEcard:(E.card:ℝ)≤aLoad^2*(Fintype.card V:ℝ)^2) (hD₀:(D₀:ℝ)≤aLoad*Fintype.card V)
    (T:Finset V) (W:Finset U) (hTI:T⊆I) (hWJ:W⊆J)
    (hTcard:(T.card:ℝ)≤θ*Fintype.card V) (hWcard:(2*W.card:ℝ)≤L)
    (hWdiv:∀u∈W,(m+1)∣(Finset.univ.filter (fun v=>H v u)).card)
    (hTbal:∀v∈T,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hErim:∀v∈T,∀w∈I,Q.Adj v w→Sum.inl s(v,w)∈E)
    (hErow:∀v∈T,∀u∈J,H v u→Sum.inr (v,u)∈E)
    (hEcol:∀u∈W,∀v∈I,H v u→Sum.inr (v,u)∈E) :
    ∃R:Finset (OrdinaryWheel Q F H (m+1)),
      (∀X∈R,∀Y∈R,X≠Y→Disjoint (ordinaryWheelResources X) (ordinaryWheelResources Y)) ∧
      R.biUnion ordinaryWheelResources∩ordinaryHostResources (spanningRestriction Q I)
        (fun v u=>H v u∧v∈I∧u∈J)=E ∧
      (∀v∈T,∀w,(ordinaryWheelRimGraph R).Adj v w↔Q.Adj v w) ∧
      (∀v∈T,∀u,ordinaryPackingSpokes R v u↔H v u) ∧
      (∀u∈W,∀v,ordinaryPackingSpokes R v u↔H v u) ∧
      (∀v∉T,((ordinaryPhysicalGraph (ordinaryWheelRimGraph R) (ordinaryPackingSpokes R)).degree (Sum.inl v):ℝ)≤
        18*aLoad*Fintype.card V+3*((W.card:ℝ)+(K+1)*T.card)) ∧
      (∀u∉W,((ordinaryPhysicalGraph (ordinaryWheelRimGraph R) (ordinaryPackingSpokes R)).degree (Sum.inr u):ℝ)≤
        3*aLoad*Fintype.card V*(m+1)+(T.card:ℝ)*(m+1)) := by
  have hFT:∀v∈T,∀w,Q.Adj v w→¬F.Adj v w:=by intro v hv w h;exact (hQ h).2
  obtain ⟨PE,hPE,hPEE,hPEone,hPEr,hPEs,hPEc,M,hM,hMr,hMs,hMc,hMd,hMrow,hMcol,hMroot,hMavoidR,hMavoidS,hMavoidC,P',hP',hP'E,hP'r,hP's,hP'c⟩:=
    hDeep Q H L (hQ.trans sdiff_le) hL hLρ hF hQR hHr hHc I hI E D₀ hE hFE hDE hEcard hD₀
      T W hTI hWJ hTcard hWcard hWdiv hFT hTbal hErim hErow hEcol
  have hME:=ordinary_deep_remainder_avoids_inner PE M I T J E hPEE hMavoidR hMavoidS hErim hErow
  obtain ⟨R,hR,hRres,hRrim,hRsp⟩:=ordinary_wheel_packing_glue PE M hPE hM
  have hRE:R.biUnion ordinaryWheelResources∩ordinaryHostResources (spanningRestriction Q I)
      (fun v u=>H v u∧v∈I∧u∈J)=E:=by
    rw [hRres,Finset.union_inter_distrib_right,Finset.disjoint_iff_inter_eq_empty.mp hME,Finset.union_empty]
    exact hPEE
  have hsubR:ordinaryWheelRimGraph PE≤Q:=ordinaryWheelRimGraph_subhost PE
  have hsubS:∀v u,ordinaryPackingSpokes PE v u→H v u:=by
    intro v u h
    obtain ⟨Y,hY,hHub,hV⟩:=h
    rw [←hHub]
    exact Y.property.1 v hV
  have hRr:∀v∈T,∀w,(ordinaryWheelRimGraph R).Adj v w↔Q.Adj v w:=by
    intro v hv w
    rw [hRrim,SimpleGraph.sup_adj,hMr v hv]
    have hh:(ordinaryWheelRimGraph PE).Adj v w→Q.Adj v w:=fun he=>hsubR he
    change _∨(Q.Adj v w∧¬_)↔Q.Adj v w
    tauto
  have hRs:∀v∈T,∀u,ordinaryPackingSpokes R v u↔H v u:=by
    intro v hv u
    rw [hRsp,hMs v hv]
    have hh:=hsubS v u
    tauto
  have hRc:∀u∈W,∀v,ordinaryPackingSpokes R v u↔H v u:=by
    intro u hu v
    rw [hRsp,hMc u hu]
    have hh:=hsubS v u
    tauto
  have hout:=ordinary_deep_union_outer_degree PE M R I J aLoad W.card T.card K hRrim hRsp hPEr hPEs
    (by intro u;convert hPEc u using 1 <;> push_cast <;> ring)
    hMd hMrow (by intro u hu;convert hMcol u hu using 1 <;> omega)
  have hinner:=ordinary_deep_union_nonroot_degree PE M R I T J W hRrim hRsp hMavoidR hMavoidS hMavoidC
  refine ⟨R,hR,hRE,hRr,hRs,hRc,?_,?_⟩
  · intro v hvT
    by_cases hvI:v∈I
    · have hv: v∈I\T:=Finset.mem_sdiff.mpr ⟨hvI,hvT⟩
      rw [hinner.1 v hv,ordinary_physical_degree_row,Nat.cast_add]
      have hpos:(0:ℝ)≤3*((W.card:ℝ)+(K+1)*T.card):=by positivity
      linarith only [hPEr v,hPEs v,hpos]
    · convert hout.1 v hvI using 1 <;> push_cast <;> ring
  · intro u huW
    by_cases huJ:u∈J
    · have hu:u∈J\W:=Finset.mem_sdiff.mpr ⟨huJ,huW⟩
      rw [hinner.2 u hu,ordinary_physical_degree_column]
      have hpos:(0:ℝ)≤(T.card:ℝ)*(m+1):=by positivity
      linarith only [hPEc u,hpos]
    · convert hout.2 u huJ using 1 <;> push_cast <;> ring
end Oberwolfach
