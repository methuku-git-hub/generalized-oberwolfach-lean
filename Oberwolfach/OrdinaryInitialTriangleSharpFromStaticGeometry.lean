module

public import Oberwolfach.OrdinaryVortexInitialTriangleFineSharpReferencePackaged
public import Oberwolfach.OrdinaryVortexInitialGeometryFromBalanceMargin

@[expose] public section
/-! Initial sharp reference on the same edited host, using the selected
static geometry and the initial balance margin. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [LinearOrder U]

theorem ordinary_initial_triangle_sharp_from_static_geometry
    (βH ηH B ρ₀ pstar βparent εparent ζ rate:ℝ) (N₀:ℕ)
    (hB:0≤B) (hρ₀:0<ρ₀) (hp:0<pstar) (hζ:0≤ζ) (hN₀:1≤N₀)
    (hscale:OrdinaryTriangleEditScaleAt βH ηH B (ρ₀/16) pstar βparent εparent ζ rate N₀)
    (k:ℕ) (hk:4≤k) (α c h δ gap lam:ℝ)
    (hroot:OrdinaryUniformFineSharpReferenceAtScaleGeneralLoad 2 k 0 (by decide) α βparent c (B/((ρ₀/16)*pstar^(2*(2+1)-1)))
      (2*h-ζ) δ εparent (ρ₀/16) gap lam)
    (P G:SimpleGraph V) (Hs:V→U→Prop) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U P D β ε m) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d:ℕ) (j:Color) (σ:RawWheelOutcome V U Γ Color) (coins:Sym2 V→Bool) (s:U→Color→ℝ)
    (βP ηP εTri pR pH ηbal Ledit ζinner:ℝ)
    (hζrate:ζinner≤rate) (hrate:0≤rate):
    let W:=markedVortexVertexType Q 0;let Z:=markedVortexHubType Q 0;
    letI : DecidableEq W:=Classical.decEq W;letI : DecidableEq Z:=Classical.decEq Z;
    let f:W↪V:=(markedVortexVertexEmbedding Q 0).toEmbedding;let g:=markedVortexHubEmbedding Q 0;
    let ρi:=markedVortexPermutation Q π hπ 0;let F:=permutationConflictGraph π (3*d);
    let raw:=ordinaryRawRestrictPair f g σ;let localCoins:=fun e:Sym2 W=>coins (Sym2.map f e);
    let Hlocal:=fun v u=>Hs (f v) (g u);let localP:=P.comap f;let localG:=G.comap f;let localF:=F.comap f;
    let I:=markedVortexInnerVertices Q 0;let T:=ordinaryVortexBufferedVertices Q 0 2;
    let J:=markedVortexInnerHubs Q 0;let Wdeep:=ordinaryVortexBufferedHubs Q 0 2;
    ∀weight:OrdinaryCycle localP (2+1)→ℝ,
    P.IsRegularOfDegree D→0<Fintype.card V→(Fintype.card V:ℝ)/2≤D→
    ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→0≤β→β≤1/4→0<ε→0<m→
    N₀≤Fintype.card W→0≤Ledit→Ledit≤ζinner*I.card→G≤P\F→
    (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
    (∀u,(2+1)∣(Finset.univ.filter (fun v=>Hs v u)).card)→
    OrdinaryDeepCoverLevelInputs 2 (2*(3*d)) d α pstar (ρ₀/16) 1 εTri localP localF ρi
      J pR pH (2*(Fintype.card Z:ℝ)/initialIndexDensity U D) β→
    pstar≤pR→pR≤1→pstar≤pH→pH≤1→0≤c→
    (∀C,c/(Fintype.card W:ℝ)^((2+1)-2)≤weight C ∧ weight C≤B/(Fintype.card W:ℝ)^((2+1)-2))→
    ordinaryCombinedTriangleEvent d k localP localF ρi (max (1/2) (cycleThreshold 3)) α pstar βP ηP ηH βH c B pR pH weight j raw→
    OrdinaryTriangleReferenceNormalizedCuts localP localF ρi d j δ h raw localCoins→
    (∀z:W⊕Z,((changed ((ordinaryPhysicalGraph (rawWheelGraph localP raw) (rawWheelSpokes ρi d raw j)).neighborFinset z)
      ((ordinaryPhysicalGraph localG Hlocal).neighborFinset z)).card:ℝ)≤Ledit)→
    0≤ηbal→
    (∀v:I,|((localG.induce (I:Set W)).degree v:ℝ)-2*(Finset.univ.filter (fun u:J=>Hlocal v.val u.val)).card|≤ηbal*I.card)→
    (∀v∉I,|((localG.neighborFinset v∩I).card:ℝ)-2*(J.filter (Hlocal v)).card|≤ηbal*I.card)→
    ∀(ξroot κ lamGeo γgeom edit βe βh εR εH βout ξ ζout p ηpack εout geomGap:ℝ),
    let deep:ℝ:=(initialIndexDensity U D*pH)*β*T.card+εR*T.card+2*(εH*Wdeep.card)+3*Ledit;
    let bin:=ηbal*I.card;let cover:=10*ξroot*I.card;let loss:=12*κ*Fintype.card W;
    let ell:=max (18*κ*Fintype.card W+3*((Wdeep.card:ℝ)+((0:ℝ)+1)*T.card))
      (3*κ*Fintype.card W*((2:ℝ)+1)+(T.card:ℝ)*((2:ℝ)+1));
    OrdinaryVortexBufferedRootStaticGeometrySeparateAtScale (2+1) k 2 ρ₀ (βparent/2)
      (c*(1-δ)^2) (B/((ρ₀/16)*pstar^(2*(2+1)-1))) (εparent+gap) geomGap
      βout ξ ζout edit p ηpack εout γgeom→
    0<γgeom→0≤lamGeo→lamGeo≤lam→lamGeo≤1/4→lamGeo≤(ρ₀/8)/2→0≤ξ→
    ε≤ξ/2→ε≤ξ*(ρ₀/8)/2→2*ε^2≤lamGeo→
    0≤βe→0≤βh→0≤εR→0≤εH→0≤ξroot→0≤κ→0<edit→
    β≤γgeom/1000→εR≤γgeom/1000→εH≤γgeom/1000→ξroot≤γgeom/160000→
    κ≤γgeom/1000→ηbal≤γgeom/1000→
    3*(((0:ℝ)+1)*lamGeo)≤edit/4→lamGeo*((2:ℝ)+1)≤edit/4→
    κ≤edit/(72*((2:ℝ)+2))→lamGeo≤βe/4→lamGeo≤βh/2→
    (initialIndexDensity U D*pH)*β*I.card+εR*I.card+2*(εH*J.card)+3*Ledit≤ηbal*I.card→
    OrdinaryFineWheelCoverResult 2 0 ξroot κ localG localF Hlocal I T J Wdeep→
    (∀v∉T,|((localG.neighborFinset v∩T).card:ℝ)-2*(Wdeep.filter (Hlocal v)).card|≤deep)→
    (T.card:ℝ)≤(βe/4)*Fintype.card (W⊕Z) ∧
    (Wdeep.card:ℝ)≤(βh/2)*Fintype.card (W⊕Z) ∧
    (T.card:ℝ)+Wdeep.card≤lamGeo*Fintype.card W ∧
    OrdinaryRootCoverSharpReferenceExists localP localG localF Hlocal I T J Wdeep (2+1) k (by decide)
      cover ell bin bin deep loss α (ρ₀/16) (βparent/2) βout (c*(1-δ)^2)
      (B/((ρ₀/16)*pstar^(2*(2+1)-1))) (2*h-ζ) (δ/2) (εparent+gap)
      ((εparent+gap)+geomGap) ηpack ξ ζout p εout (deep+2*cover) (bin+deep+4*cover) (bin+deep+loss) :=by
  intro W Z f g ρi F raw localCoins Hlocal localP localG localF I T J Wdeep weight
    hreg hn hD hρlo hρhi hβ hβ1 hε hm hN hL hLinner hhost hbal hdiv hinputs
    hRlo hRhi hHlo hHhi hc hweight event cuts hphysical hηbal hnear hcross
    ξroot κ lamGeo γgeom edit βe βh εR εH βout ξ ζout p ηpack εout geomGap deep bin cover loss ell
    hgeometry hγ hlam hlamRoot hlam1 hlamρ hξ hεξ hερ hεroot hβe hβh hεR hεH hξroot hκ hedit
    hβcap hRcap hHcap hξcap hκcap hηcap hrow hlevel hκedit hTcap hWcap hmargin hcover hdeep
  have hLrate:Ledit≤rate*Fintype.card W:=by
    have hI:(I.card:ℝ)≤Fintype.card W:=by exact_mod_cast Finset.card_le_univ I
    exact hLinner.trans ((mul_le_mul_of_nonneg_right hζrate (by positivity)).trans
      (mul_le_mul_of_nonneg_left hI hrate))
  have hGP:G≤P:=hhost.trans sdiff_le
  have hdis:Disjoint G F:=by
    apply disjoint_iff_inf_le.mpr
    intro v w hvw
    exact (hhost hvw.1).2 hvw.2
  have hgeom:=ordinary_vortex_initial_geometry_from_balance_margin 2 0 k β ε ρ₀ lamGeo ξ ξroot κ ηbal γgeom edit p
    βe βh pH εR εH Ledit (βparent/2) (c*(1-δ)^2) (B/((ρ₀/16)*pstar^(2*(2+1)-1)))
    (εparent+gap) geomGap βout ζout ηpack εout hgeometry hβ hβ1 hε hρ₀ hγ hlam hlam1 hlamρ
    hξ hεξ hερ hεroot hβe hβh (hp.le.trans hHlo) hHhi hεR hεH hξroot hκ hηbal hL hedit
    hβcap hRcap hHcap hξcap hκcap hηcap (by simpa using hrow) hlevel hκedit hTcap hWcap
    V U P D m hreg hn hD hρlo hρhi hm Q hmargin
  obtain ⟨hsize,hT,hW,hdeep0,hbin0,_,hstatic,hscaleV,hscaleU⟩:=hgeom
  have hsizeRoot:(T.card:ℝ)+Wdeep.card≤lam*Fintype.card W:=
    hsize.trans (mul_le_mul_of_nonneg_right hlamRoot (by positivity))
  have hcall:=ordinary_vortex_initial_triangle_fine_sharp_reference_packaged 2 (by omega) βH ηH B ρ₀ pstar
    βparent εparent ζ rate N₀ hB hρ₀ hp hζ hN₀ hscale k hk α c h δ gap lam hroot P G Hs D m β ε Q π hπ d j σ coins s
    βP ηP εTri pR pH ηbal Ledit weight hreg hn hD hρlo hρhi hβ hβ1 hε hm hN hL hLrate hGP hdis hbal hdiv hinputs
    hRlo hRhi hHlo hHhi hc hweight event cuts hphysical hηbal hnear hcross
  have href:=hcall ξroot κ bin bin deep (ρ₀/16) βout ((εparent+gap)+geomGap) ηpack ξ ζout p εout
    (by convert hsizeRoot using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _) hξroot hκ
    (by dsimp [bin]; positivity) hdeep0 (by rfl) (by rfl) hcover hdeep
    (by convert hstatic using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    (by convert hscaleV using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
    (by convert hscaleU using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _)
  refine ⟨?_,?_,?_,?_⟩
  · convert hT using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _
  · convert hW using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _
  · convert hsize using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _
  · convert href using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _
end Oberwolfach
