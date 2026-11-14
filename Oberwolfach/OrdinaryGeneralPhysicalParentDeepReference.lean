module

public import Oberwolfach.OrdinaryGeneralEditedParentPhysicalAtScale
public import Oberwolfach.OrdinaryUniformDeepRootReferenceAtScale
public import Oberwolfach.OrdinaryInducedBalanceToSpanning
public import Oberwolfach.OrdinaryCrossBalanceCardBound

@[expose] public section
/-! An actual physical edit, local balance, and a root cover produce the
general-wheel deep reference on the same sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_general_physical_parent_deep_reference
    (m d k:ℕ) (hm:3≤m) (hk:4≤k) (P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V)
    (α pstar βP ηP row ηH βH c B pR pH ω βparent h ζ δ εparent rate L gap lam:ℝ) (N₀:ℕ)
    (hscale:OrdinaryGeneralEditScaleAt (m+1) βH ηH B ω pstar βparent εparent ζ rate N₀)
    (hroot:OrdinaryUniformDeepRootReferenceAtScale (m+1) (by omega) k α βparent c (B/(ω*pstar^(2*(m+1)-1)))
      (2*h-ζ) δ εparent ω gap lam)
    (weight:OrdinaryCycle P (m+1)→ℝ) (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color) (coins:Sym2 V→Bool)
    (hN:N₀≤Fintype.card V) (hN₀:1≤N₀) (hu:0<Fintype.card U) (hUhi:Fintype.card U≤Fintype.card V)
    (hω:0<ω) (hp:0<pstar) (hUlo:ω*Fintype.card V≤Fintype.card U)
    (hRlo:pstar≤pR) (hRhi:pR≤1) (hHlo:pstar≤pH) (hHhi:pH≤1)
    (hc:0≤c) (hB:0≤B) (hζ:0≤ζ) (hL:0≤L) (hLrate:L≤rate*Fintype.card V) (hQP:Q≤P\F)
    (hw:∀C,c/(Fintype.card V:ℝ)^((m+1)-2)≤weight C ∧ weight C≤B/(Fintype.card V:ℝ)^((m+1)-2))
    (event:ordinaryCombinedHostEvent m d k hm P F π (max (1/2) (cycleThreshold (m+1))) α pstar βP ηP row ηH βH c B pR pH weight s j raw)
    (cuts:OrdinaryTriangleReferenceNormalizedCuts P F π d j δ h raw coins)
    (hphysical:∀z:V⊕U,((changed ((ordinaryPhysicalGraph (rawWheelGraph P raw) (rawWheelSpokes π d raw j)).neighborFinset z)
      ((ordinaryPhysicalGraph Q H).neighborFinset z)).card:ℝ)≤L)
    (X T:Finset V) (Z W:Finset U) (ηcover ell bin cin deep:ℝ)
    (Droot:OrdinaryRootCoverNonrootData Q F H X T Z W (m+1) ηcover ell)
    (ωout βout εstar η ξ ζout p εout fout binner cross:ℝ)
    (hsize:(T.card:ℝ)+W.card≤lam*Fintype.card V) (hell:0≤ell)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,(m+1)∣(Finset.univ.filter (fun v=>H v u)).card)
    (hTX:T⊆X) (hWZ:W⊆Z) (hdeep:(T.card:ℝ)+2*W.card≤deep)
    (hbin:0≤bin)
    (hnear:∀v:X,|((Q.induce (X:Set V)).degree v:ℝ)-2*(Finset.univ.filter (fun u:Z=>H v.val u.val)).card|≤bin)
    (hcross:∀v∉X,|((Q.neighborFinset v∩X).card:ℝ)-2*(Z.filter (H v)).card|≤cin)
    (hfull:deep+3*ell≤fout) (hinnermargin:bin+3*ell+(deep+3*ell)≤binner)
    (hcrossmargin:cin+3*ell+(deep+3*ell)≤cross):
    let A:=Finset.univ\T;let C:=Finset.univ\W;
    let Xf:Finset A:=Finset.univ.filter (fun v=>v.val∈X);
    let Zf:Finset C:=Finset.univ.filter (fun u=>u.val∈Z);
    OrdinaryNonrootGeometryStatic (m+1) k ωout (βparent/2) βout (c*(1-δ)^((m+1)-1))
      (B/(ω*pstar^(2*(m+1)-1))) (εparent+gap) εstar η ξ ζout p εout fout binner cross Xf Zf→
    ell+(p+εout)*Fintype.card (A⊕C)≤ζout*Fintype.card A→
    ell+(p+εout)*Fintype.card (A⊕C)≤ζout*Fintype.card C→
    Nonempty (OrdinaryRootCoverDeepReferenceData P Q F H X T Z W (m+1) k (by omega) ηcover ell bin cin deep Droot
      α ωout (βparent/2) βout (c*(1-δ)^((m+1)-1)) (B/(ω*pstar^(2*(m+1)-1)))
      (2*h-ζ) (δ/2) (εparent+gap) εstar η ξ ζout p εout fout binner cross) :=by
  intro A C Xf Zf hstatic hscaleV hscaleU
  obtain ⟨parent⟩:=ordinary_general_edited_parent_physical_at_scale m d k hm hk P Q F H π
    α pstar βP ηP row ηH βH c B pR pH ω βparent h ζ δ εparent rate L N₀ hscale weight s j raw coins
    hN hN₀ hu hUhi hω hp hUlo hRlo hRhi hHlo hHhi hc hB hζ hL hLrate hQP hw event cuts hphysical
  have hn:0<Fintype.card V:=by omega
  have hinner:=ordinary_induced_balance_to_spanning Q H X Z bin hbin hnear
  have hdeepbal:∀v∉T,|((Q.neighborFinset v∩T).card:ℝ)-2*(W.filter (H v)).card|≤deep:=by
    intro v hv
    exact (ordinary_cross_balance_card_bound Q H T W v).trans hdeep
  exact hroot V U P Q F H parent X T Z W ηcover ell bin cin deep Droot ωout βout εstar η ξ ζout p εout fout binner cross
    hn hu hUhi hUlo hsize hell hQP hbal hdiv hTX hWZ hdeepbal hinner hcross hfull hinnermargin hcrossmargin
    hstatic hscaleV hscaleU
end Oberwolfach
