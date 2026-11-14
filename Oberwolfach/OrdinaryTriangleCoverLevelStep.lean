module

public import Oberwolfach.OrdinaryTriangleFiniteCoverEvent
public import Oberwolfach.OrdinaryWheelLevelStep

@[expose] public section
/-! Turn the triangle finite-cover event into an exact level step on the
same sample, retaining the prescribed protected resources. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [LinearOrder U]

theorem ordinary_triangle_cover_event_level_step
    (κ:ℝ) (P F Ambient:SimpleGraph V) (J:Finset U)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (σ:RawWheelOutcome V U Γ Color)
    (hDeep:OrdinaryTriangleFiniteCoverEvent κ P F J π d j σ)
    (Q:SimpleGraph V) (H Hambient:V→U→Prop) (L:ℝ)
    (hQP:Q≤P\F) (hQA:Q≤Ambient) (hHA:∀v u,H v u→Hambient v u)
    (hL:0≤L) (hLρ:L≤κ*Fintype.card V) (hF:∀v,(F.degree v:ℝ)≤L)
    (hQR:∀v,((changed ((rawWheelGraph P σ).neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L)
    (hHr:∀v,((changed (Finset.univ.filter (rawWheelSpokes π d σ j v)) (Finset.univ.filter (H v))).card:ℝ)≤L)
    (hHc:∀u,((changed (Finset.univ.filter (fun v=>rawWheelSpokes π d σ j v u))
      (Finset.univ.filter (fun v=>H v u))).card:ℝ)≤L)
    (I:Finset V) (hI:(I.card:ℝ)≤κ*Fintype.card V)
    (E:Finset (Sym2 V⊕(V×U))) (D₀:ℕ)
    (hE:E⊆ordinaryHostResources (spanningRestriction Q I) (fun v u=>H v u∧v∈I∧u∈J))
    (hFE:∀v w,Sum.inl s(v,w)∈E→¬F.Adj v w)
    (hDE:∀t,(E.filter (ordinaryResourceIncident t)).card≤D₀)
    (hEcard:(E.card:ℝ)≤κ^2*(Fintype.card V:ℝ)^2) (hD₀:(D₀:ℝ)≤κ*Fintype.card V)
    (T:Finset V) (W:Finset U) (hTI:T⊆I) (hWJ:W⊆J)
    (hTcard:(T.card:ℝ)≤κ*Fintype.card V) (hWcard:(2*W.card:ℝ)≤L)
    (hWdiv:∀u∈W,3∣(Finset.univ.filter (fun v=>H v u)).card)
    (hTbal:∀v∈T,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hErim:∀v∈T,∀w∈I,Q.Adj v w→Sum.inl s(v,w)∈E)
    (hErow:∀v∈T,∀u∈J,H v u→Sum.inr (v,u)∈E)
    (hEcol:∀u∈W,∀v∈I,H v u→Sum.inr (v,u)∈E)
    (IV:Finset V) (IU:Finset U) (hroot:ordinaryHostResources Q H⊆ordinaryRootResources IV IU):
    let S:=ordinaryHostResources Q H;
    ∃ M:Finset (OrdinaryWheel Q F H 3),
      M.biUnion ordinaryWheelResources∩ordinaryHostResources (spanningRestriction Q I)
        (fun v u=>H v u∧v∈I∧u∈J)=E ∧
      let Next:=S\M.biUnion ordinaryWheelResources;
      Next⊆S ∧ Next⊆ordinaryRootResources (IV\T) (IU\W) ∧
      HasResourceDecomposition (ordinaryWheelResources (P:=Ambient) (F:=F) (Hbase:=Hambient) (r:=3)) (S\Next):=by
  intro S
  obtain ⟨M,hM,hpres,hrim,hrow,hcol⟩:=
    hDeep Q H L hQP hL hLρ hF hQR hHr hHc I hI E D₀ hE hFE hDE hEcard hD₀
      T W hTI hWJ hTcard hWcard hWdiv hTbal hErim hErow hEcol
  have hstep:=ordinary_wheel_packing_level_step Q Ambient F H Hambient 3 hQA hHA IV IU T W hroot M hM hrim hrow hcol
  exact ⟨M,hpres,hstep⟩
end Oberwolfach
