module

public import Oberwolfach.OrdinaryVortexInitialFineSharpReferenceGeneralLoad
public import Oberwolfach.OrdinaryInducedBalanceToSpanning
public import Oberwolfach.OrdinaryVortexInitialBufferedReferenceFromCover
public import Oberwolfach.MixedFreshPairingParentInsideRoots
public import Oberwolfach.OrdinaryGeneralPhysicalParentDeepReference
public import Oberwolfach.OrdinaryVortexBufferedGeneralRootGeometryWithSlackAtScale
public import Oberwolfach.OrdinaryGeneralDeepInputsFixedDomain
public import Oberwolfach.OrdinaryVortexSupportedLocalExactBalance

@[expose] public section
/-! At any vortex level, actual local sample edits and both local balances
combine with the buffered cover into the general-wheel reference. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [LinearOrder U]

theorem ordinary_vortex_local_fine_sharp_reference_general_load
    (mWheel loadK buffer:ℕ) (hmWheel:3≤mWheel) (hbuffer:2≤buffer)
    (βH ηH B ρ₀ pstar βparent εparent ζ rate:ℝ) (N₀:ℕ)
    (hB:0≤B) (hρ₀:0<ρ₀) (hp:0<pstar) (hζ:0≤ζ) (hN₀:1≤N₀)
    (hscale:OrdinaryGeneralEditScaleAt (mWheel+1) βH ηH B (ρ₀/16) pstar βparent εparent ζ rate N₀)
    (k:ℕ) (hk:4≤k) (α c h δ gap lam:ℝ)
    (hroot:OrdinaryUniformFineSharpReferenceAtScaleGeneralLoad mWheel k loadK (by omega) α βparent c (B/((ρ₀/16)*pstar^(2*(mWheel+1)-1)))
      (2*h-ζ) δ εparent (ρ₀/16) gap lam)
    (P G:SimpleGraph V) (Hs:V→U→Prop) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U P D β ε m) (i:ℕ) (hi:i<Q.length) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d:ℕ) (j:Color) (σ:RawWheelOutcome V U Γ Color) (coins:Sym2 V→Bool) (s:U→Color→ℝ)
    (βP ηP row εTri pR pH ηbal Ledit:ℝ):
    let W:=markedVortexVertexType Q i;let Z:=markedVortexHubType Q i;
    letI : DecidableEq W:=Classical.decEq W;letI : DecidableEq Z:=Classical.decEq Z;
    let f:W↪V:=(markedVortexVertexEmbedding Q i).toEmbedding;let g:=markedVortexHubEmbedding Q i;
    let ρi:=markedVortexPermutation Q π hπ i;let F:=permutationConflictGraph π (3*d);
    let raw:=ordinaryRawRestrictPair f g σ;let localCoins:=fun e:Sym2 W=>coins (Sym2.map f e);
    let Hlocal:=fun v u=>Hs (f v) (g u);let localP:=P.comap f;let localG:=G.comap f;let localF:=F.comap f;
    let I:=markedVortexInnerVertices Q i;let T:=ordinaryVortexBufferedVertices Q i buffer;
    let J:=markedVortexInnerHubs Q i;let Wdeep:=ordinaryVortexBufferedHubs Q i buffer;
    ∀weight:OrdinaryCycle localP (mWheel+1)→ℝ,
    P.IsRegularOfDegree D→0<Fintype.card V→(Fintype.card V:ℝ)/2≤D→
    ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→0≤β→β≤1/4→0<ε→0<m→
    N₀≤Fintype.card W→0≤Ledit→Ledit≤rate*Fintype.card W→localG≤localP\localF→
    (∀v,localG.degree v=2*(Finset.univ.filter (Hlocal v)).card)→
    (∀u,(mWheel+1)∣(Finset.univ.filter (fun v=>Hlocal v u)).card)→
    OrdinaryDeepCoverLevelInputs mWheel (2*(3*d)) d α pstar (ρ₀/16) 1 εTri localP localF ρi
      J pR pH (2*(Fintype.card Z:ℝ)/initialIndexDensity U D) β→
    pstar≤pR→pR≤1→pstar≤pH→pH≤1→0≤c→
    (∀C,c/(Fintype.card W:ℝ)^((mWheel+1)-2)≤weight C ∧ weight C≤B/(Fintype.card W:ℝ)^((mWheel+1)-2))→
    ordinaryCombinedHostEvent mWheel d k hmWheel localP localF ρi (max (1/2) (cycleThreshold (mWheel+1))) α pstar βP ηP row ηH βH c B pR pH weight (fun u=>s (g u)) j raw→
    OrdinaryTriangleReferenceNormalizedCuts localP localF ρi d j δ h raw localCoins→
    (∀z:W⊕Z,((changed ((ordinaryPhysicalGraph (rawWheelGraph localP raw) (rawWheelSpokes ρi d raw j)).neighborFinset z)
      ((ordinaryPhysicalGraph localG Hlocal).neighborFinset z)).card:ℝ)≤Ledit)→
    0≤ηbal→
    (∀v:I,|((localG.induce (I:Set W)).degree v:ℝ)-2*(Finset.univ.filter (fun u:J=>Hlocal v.val u.val)).card|≤ηbal*I.card)→
    (∀v∉I,|((localG.neighborFinset v∩I).card:ℝ)-2*(J.filter (Hlocal v)).card|≤ηbal*I.card)→
    ∀(ξroot κ bin cin deep ω βout εstar η ξ ζout p εout:ℝ),
    (T.card:ℝ)+Wdeep.card≤lam*Fintype.card W→0≤ξroot→0≤κ→0≤bin→0≤deep→
    ηbal*I.card≤bin→ηbal*I.card≤cin→
    OrdinaryFineWheelCoverResult mWheel loadK ξroot κ localG localF Hlocal I T J Wdeep→
    (∀v∉T,|((localG.neighborFinset v∩T).card:ℝ)-2*(Wdeep.filter (Hlocal v)).card|≤deep)→
    let ell:=max (18*κ*Fintype.card W+3*((Wdeep.card:ℝ)+((loadK:ℝ)+1)*T.card))
      (3*κ*Fintype.card W*((mWheel:ℝ)+1)+(T.card:ℝ)*((mWheel:ℝ)+1));
    let cover:=10*ξroot*I.card;let loss:=12*κ*Fintype.card W;
    let fout:=deep+2*cover;let binner:=bin+deep+4*cover;let cross:=cin+deep+loss;
    let Aroot:=Finset.univ\T;let Croot:=Finset.univ\Wdeep;
    let Xf:Finset Aroot:=Finset.univ.filter (fun v=>v.val∈I);
    let Zf:Finset Croot:=Finset.univ.filter (fun u=>u.val∈J);
    OrdinaryNonrootGeometryStatic (mWheel+1) k ω (βparent/2) βout (c*(1-δ)^mWheel)
      (B/((ρ₀/16)*pstar^(2*(mWheel+1)-1))) (εparent+gap) εstar η ξ ζout p εout fout binner cross Xf Zf→
    ell+(p+εout)*Fintype.card (Aroot⊕Croot)≤ζout*Fintype.card Aroot→
    ell+(p+εout)*Fintype.card (Aroot⊕Croot)≤ζout*Fintype.card Croot→
    ∃Droot:OrdinaryRootCoverNonrootData localG localF Hlocal I T J Wdeep (mWheel+1) cover ell,
    Nonempty (OrdinaryRootCoverSharpReferenceData localP localG localF Hlocal I T J Wdeep (mWheel+1) k (by omega)
      cover ell bin cin deep loss Droot α ω (βparent/2) βout (c*(1-δ)^mWheel)
      (B/((ρ₀/16)*pstar^(2*(mWheel+1)-1))) (2*h-ζ) (δ/2) (εparent+gap)
      εstar η ξ ζout p εout fout binner cross) :=by
  intro W Z f g ρi F raw localCoins Hlocal localP localG localF I T J Wdeep weight
    hreg hn hD hρlo hρhi hβ hβ1 hε hm hN hL hLrate hhost hbal hdiv hinputs
    hRlo hRhi hHlo hHhi hc hweight event cuts hphysical hηbal hnear hcross
    ξroot κ bin cin deep ω βout εstar η ξ ζout p εout hsize hξ hκ hbin hdeep0 hbinMargin hcinMargin hcover hdeep
    ell cover loss fout binner cross Aroot Croot Xf Zf hstatic hscaleV hscaleU
  have hW:0<Fintype.card W:=by omega
  have hfields:=ordinary_general_deep_inputs_fixed_domain mWheel (2*(3*d)) d (by omega) α pstar (ρ₀/16) 1 εTri
    localP localF ρi J pR pH (2*(Fintype.card Z:ℝ)/initialIndexDensity U D) β
    (by convert hinputs using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  have hU:0<Fintype.card Z:=by
    have hWr:(0:ℝ)<Fintype.card W:=by exact_mod_cast hW
    have hh:0<(Fintype.card Z:ℝ):=(mul_pos (by positivity : (0:ℝ)<ρ₀/16) hWr).trans_le hfields.1
    exact_mod_cast hh
  obtain ⟨parent⟩:=ordinary_general_edited_parent_physical_at_scale mWheel d k hmWheel hk localP localG localF Hlocal ρi
    α pstar βP ηP row ηH βH c B pR pH (ρ₀/16) βparent h ζ δ εparent rate Ledit N₀ hscale weight
    (fun u=>s (g u)) j raw localCoins hN hN₀ hU hfields.2.1 (by positivity) hp hfields.1
    hRlo hRhi hHlo hHhi hc hB hζ hL hLrate hhost hweight
    (by convert event using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by convert cuts using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro z;convert hphysical z using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  have hTX:T⊆I:=(ordinary_vortex_buffered_nested Q i buffer (by omega)).2.2.1
  have hWJ:Wdeep⊆J:=(ordinary_vortex_buffered_nested Q i buffer (by omega)).2.2.2
  have hinner0:=ordinary_induced_balance_to_spanning localG Hlocal I J (ηbal*I.card) (by positivity) hnear
  have hinner:∀v,|((spanningRestriction localG I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>Hlocal v u∧v∈I∧u∈J)).card|≤bin:=by
    intro v
    convert (hinner0 v).trans hbinMargin using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hcross':∀v∉I,|((localG.neighborFinset v∩I).card:ℝ)-2*(J.filter (Hlocal v)).card|≤cin:=by
    intro v hv
    convert (hcross v hv).trans hcinMargin using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have href:=hroot W Z localP localG localF Hlocal
    (by convert parent using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) I T J Wdeep ξroot κ bin cin deep
    hTX hWJ hξ hκ hbin hdeep0 hW hU hfields.2.1 hfields.1 hsize hcover hhost
    (by convert hbal using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by convert hdiv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro v hv;convert hdeep v hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro v;convert hinner v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro v hv;convert hcross' v hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    ω βout εstar η ξ ζout p εout
    (by convert hstatic using 1 <;> congr! 8 <;> first | exact Subsingleton.elim _ _ | (ext x; simp))
    (by convert hscaleV using 1 <;> congr! 8 <;> first | exact Subsingleton.elim _ _ | (ext x; simp))
    (by convert hscaleU using 1 <;> congr! 8 <;> first | exact Subsingleton.elim _ _ | (ext x; simp))
  obtain ⟨Droot,hRef⟩:=href
  exact ⟨Droot,hRef⟩
end Oberwolfach
