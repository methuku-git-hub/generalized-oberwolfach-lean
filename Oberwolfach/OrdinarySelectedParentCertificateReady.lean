module

public import Oberwolfach.OrdinarySelectedParentCertificateParameters
public import Oberwolfach.OrdinarySelectedParentCertificateBounds
public import Oberwolfach.OrdinarySelectedCertificateMatchingThreshold

@[expose] public section
/-! One selected parent certificate, its packing margin, finish cap and
pre-sample threshold serve both the initial and every later level. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_selected_parent_certificate_ready
    (mWheel loadK k d n₀ Nclean Nreserve Ncert:ℕ) (hm:3≤mWheel)
    (α ρ₀ pstar βout cParent Bhost hParent δparent εparent gapParent geomGap:ℝ)
    (ηpack γcert b Bweight pmin κ ηHub ζhub ζlocal δend:ℝ)
    (p βe βh ν cap εsup δsample τ εout:ℝ)
    (ζparent geomCap ξreserve ζout ε cMatch θmatch kcap η:ℝ) (Nfinish Nextra:ℕ)
    (hζ:ζparent≤hParent) (hgeom:2*geomCap≤hParent/2)
    (hξ:ξreserve≤geomCap) (hout:ζout≤geomCap)
    (hε:0<ε) (hρ:0<ρ₀) (hkcap:0<kcap) (hη:0<η)
    (hθ:θmatch=cMatch*ε)
    (hmatch:cMatch≤min (ζhub*γcert*(1/4:ℝ)) (ζlocal*(1/4:ℝ))/2):
    let s:=ordinarySelectedParentCertificateParameters mWheel loadK k d n₀ Nclean Nreserve Ncert hm
      α ρ₀ pstar βout cParent Bhost hParent δparent εparent gapParent geomGap
      ηpack γcert b Bweight pmin κ ηHub ζhub ζlocal δend p βe βh ν cap εsup δsample τ εout;
    OrdinaryVortexFineCertificateAtGeneralLoad s→
    OrdinaryVortexFineCertificateAtGeneralLoad s ∧
    s.hpack≤(2*hParent-ζparent)-ξreserve-ζout ∧
    θmatch≤(min (s.ζhub*s.γ*(1/4:ℝ)) (s.ζlocal*(1/4:ℝ))/2)*ε ∧
    let Nbase:=max (max (max (4*s.n₀) (4*s.Nreserve)) (max s.Nclean 64)) (max s.Ncert Nfinish);
    ∃M:ℕ,1≤M ∧ Nbase≤M ∧ Nextra≤M ∧ 4/ε≤(M:ℝ) ∧ s.L≤kcap^2*M ∧
    (∀n:ℕ,M≤n→∀cost:ℝ,cost≤14*η*n→cost+2*((3*d:ℕ):ℝ)≤15*η*n) ∧
    ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (P:SimpleGraph V) (D mv:ℕ) (β:ℝ),
      P.IsRegularOfDegree D→0<Fintype.card V→(Fintype.card V:ℝ)/2≤D→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→0≤β→β≤1/4→0<mv→
      (M:ℝ)≤ε*mv/2→∀(Q:Vortex U P D β ε mv) (i:ℕ),i<Q.length→
      let I:=markedVortexInnerVertices Q i;
      I.Nonempty ∧ Nbase≤I.card ∧ M≤I.card ∧
        s.L≤kcap^2*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i) :=by
  intro s hcert
  have hmatch':cMatch≤min (s.ζhub*s.γ*(1/4:ℝ)) (s.ζlocal*(1/4:ℝ))/2:=by
    simpa [s,ordinarySelectedParentCertificateParameters] using hmatch
  have hb:=ordinary_selected_parent_certificate_bounds s hParent ζparent geomCap ξreserve ζout ε cMatch θmatch
    rfl hζ hgeom hξ hout hε.le hθ hmatch'
  exact ⟨hcert,hb.1,hb.2,ordinary_selected_certificate_matching_threshold s ε ρ₀ kcap η d Nfinish Nextra hε hρ hkcap hη⟩
end Oberwolfach
