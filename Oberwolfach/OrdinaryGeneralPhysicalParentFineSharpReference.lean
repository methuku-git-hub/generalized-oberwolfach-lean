module

public import Oberwolfach.OrdinaryGeneralEditedParentPhysicalAtScale
public import Oberwolfach.OrdinaryFineCoverSharpReference
public import Oberwolfach.OrdinaryInducedBalanceToSpanning

@[expose] public section
/-! The edited physical parent and its actual fine wheel cover produce the
sharp restricted reference for the same sampled host and coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [LinearOrder U]

theorem ordinary_general_physical_parent_fine_sharp_reference
    (m d k:ℕ) (hm:3≤m) (hk:4≤k) (P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V)
    (α pstar βP ηP row ηH βH c B pR pH ω βparent h ζ δ εparent rate L gap:ℝ) (N₀:ℕ)
    (hscale:OrdinaryGeneralEditScaleAt (m+1) βH ηH B ω pstar βparent εparent ζ rate N₀)
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
    (X T:Finset V) (Z W:Finset U) (ξroot κ bin cin deep:ℝ)
    (hTX:T⊆X) (hWZ:W⊆Z) (hξ:0≤ξroot) (hκ:0≤κ) (hbin:0≤bin) (hdeep0:0≤deep)
    (hcover:OrdinaryFineWheelCoverResult m 0 ξroot κ Q F H X T Z W)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,(m+1)∣(Finset.univ.filter (fun v=>H v u)).card)
    (hdeep:∀v∉T,|((Q.neighborFinset v∩T).card:ℝ)-2*(W.filter (H v)).card|≤deep)
    (hnear:∀v:X,|((Q.induce (X:Set V)).degree v:ℝ)-2*(Finset.univ.filter (fun u:Z=>H v.val u.val)).card|≤bin)
    (hcross:∀v∉X,|((Q.neighborFinset v∩X).card:ℝ)-2*(Z.filter (H v)).card|≤cin)
    (ωout βout εstar η ξ ζout p εout:ℝ):
    let ell:=max (18*κ*Fintype.card V+3*((W.card:ℝ)+(((0:ℕ):ℝ)+1)*T.card))
      (3*κ*Fintype.card V*((m:ℝ)+1)+(T.card:ℝ)*((m:ℝ)+1));
    let cover:=10*ξroot*X.card;let loss:=12*κ*Fintype.card V;
    let f:=deep+2*cover;let binner:=bin+deep+4*cover;let cross:=cin+deep+loss;
    let A:=Finset.univ\T;let C:=Finset.univ\W;
    let Xf:Finset A:=Finset.univ.filter (fun v=>v.val∈X);
    let Zf:Finset C:=Finset.univ.filter (fun u=>u.val∈Z);
    (OrdinaryEditedParentFields (m+1) (by omega) k α βparent c (B/(ω*pstar^(2*(m+1)-1))) (2*h-ζ) δ εparent P Q F H→
      Nonempty (OrdinaryEditedParentFields (m+1) (by omega) k α (βparent/2) (c*(1-δ)^m)
        (B/(ω*pstar^(2*(m+1)-1))) (2*h-ζ) (δ/2) (εparent+gap)
        (P.induce (A:Set V)) (Q.induce (A:Set V)) (F.induce (A:Set V))
        (fun (v:A) (u:C)=>H v.val u.val)))→
    OrdinaryNonrootGeometryStatic (m+1) k ωout (βparent/2) βout (c*(1-δ)^m)
      (B/(ω*pstar^(2*(m+1)-1))) (εparent+gap) εstar η ξ ζout p εout f binner cross Xf Zf→
    ell+(p+εout)*Fintype.card (A⊕C)≤ζout*Fintype.card A→
    ell+(p+εout)*Fintype.card (A⊕C)≤ζout*Fintype.card C→
    ∃Droot:OrdinaryRootCoverNonrootData Q F H X T Z W (m+1) cover ell,
    Nonempty (OrdinaryRootCoverSharpReferenceData P Q F H X T Z W (m+1) k (by omega) cover ell bin cin deep loss Droot
      α ωout (βparent/2) βout (c*(1-δ)^m) (B/(ω*pstar^(2*(m+1)-1)))
      (2*h-ζ) (δ/2) (εparent+gap) εstar η ξ ζout p εout f binner cross):=by
  intro ell cover loss f binner cross A C Xf Zf hrestrict hstatic hscaleV hscaleU
  obtain ⟨parent⟩:=ordinary_general_edited_parent_physical_at_scale m d k hm hk P Q F H π
    α pstar βP ηP row ηH βH c B pR pH ω βparent h ζ δ εparent rate L N₀ hscale weight s j raw coins
    hN hN₀ hu hUhi hω hp hUlo hRlo hRhi hHlo hHhi hc hB hζ hL hLrate hQP hw event cuts hphysical
  obtain ⟨fields⟩:=hrestrict parent
  have hinner:=ordinary_induced_balance_to_spanning Q H X Z bin hbin hnear
  exact ordinary_fine_cover_sharp_reference m k (by omega) ξroot κ P Q F H X T Z W hTX hWZ hξ hκ bin cin deep hbin hdeep0
    hcover hQP hbal hdiv hdeep hinner hcross α ωout (βparent/2) βout (c*(1-δ)^m)
    (B/(ω*pstar^(2*(m+1)-1))) (2*h-ζ) (δ/2) (εparent+gap) εstar η ξ ζout p εout fields hstatic hscaleV hscaleU
end Oberwolfach
