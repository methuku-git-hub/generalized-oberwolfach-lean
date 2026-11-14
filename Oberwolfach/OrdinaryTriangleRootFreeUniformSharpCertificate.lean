module

public import Oberwolfach.OrdinaryTriangleRootFreeRateActualCover
public import Oberwolfach.OrdinaryTriangleRootFreeLocalSizes
public import Oberwolfach.OrdinaryRootCoverSharpReferenceExists

@[expose] public section
/-! A single size threshold makes the selected actual-cover callback usable
for every local host; the ordinary and deep certificate costs remain distinct. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_root_free_uniform_sharp_certificate
    (α:ℝ) (k:ℕ) (hk:4≤k) (ω β b B hpack δref εstar cLinear κe pmin bHub BHub εf ηhub ηend ζfresh εrows:ℝ)
    (p βe βh ν cap εsup δsample τ:ℝ)
    (hfixed:OrdinaryTriangleRootFreeActualCoverAfterCleanup α k ω β b B hpack δref εstar cLinear κe pmin
      bHub BHub εf ηhub ηend ζfresh εrows p βe βh ν cap εsup δsample τ)
    (b₀:ℕ) (L:ℝ) (hL:0≤L) (eps:ℝ) (heps:0<eps):
    ∃M:ℕ,64≤M ∧
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [LinearOrder U],
    ∀(P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ)
      (X T:Finset V) (Z W:Finset U)
      (ξroot aLoad lam ellCap ηCap b₁ c₁ deep crossLoss:ℝ)
      (βparent h εparent ξ ζ f binner c:ℝ)
      (pR pH density tR tH tP Ledit βe₀ βh₀ δbal K γold κold bold Bold εold:ℝ)
      (s:U→Color→ℝ) (j:Color) (weight:V→Sym2 (V⊕U)→ℝ) (raw:RawWheelOutcome V U Γ Color),
    let cover:=10*ξroot*X.card;
    let ell:=max (18*aLoad*Fintype.card V+3*((W.card:ℝ)+T.card))
      (3*aLoad*Fintype.card V*3+(T.card:ℝ)*3);
    M≤X.card→0<Fintype.card V→(T.card:ℝ)+W.card≤lam*Fintype.card V→lam≤1/4→
    0≤ξroot→0≤aLoad→0≤lam→0≤ellCap→0≤ηCap→
    max (18*aLoad+3*lam) ((3*aLoad+lam)*3)≤ellCap→10*ξroot≤ηCap→
    OrdinaryRootCoverSharpReferenceExists P Q F H X T Z W 3 k (by omega)
      cover ell b₁ c₁ deep crossLoss α ω βparent β b B h δref εparent εstar (cLinear*τ) ξ ζ p eps f binner c→
    hpack≤h-ξ-ζ→T⊆X→W⊆Z→
    (T.card:ℝ)≤(βe/2)*Fintype.card (V⊕U)→
    (W.card:ℝ)≤(βh/2)*Fintype.card (V⊕U)→Disjoint Q F→
    Fintype.card {v:V // v∉X}≤X.card^2→Fintype.card {u:U // u∉Z}≤X.card^2→
    OrdinaryDeepParentIngredients P Q F H X Z π d j s weight γold κold bold Bold εold ηend κe pmin
      pR pH density tR tH L Ledit βe₀ βh₀ δbal εrows tP K raw→
    OrdinaryMixedHubWeightsInnerScale 2 bHub BHub ηhub Q F H X Z→
    (∀v,F.degree v≤b₀)→L≤εf*X.card→
    (∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)→
    (∀u,3∣(Finset.univ.filter (fun v=>H v u)).card)→
    ∀κscale rate:ℝ,
    OrdinaryTriangleRootFirstScaledConditions Q H X Z p εsup τ ν ηCap (p*ellCap+δsample) κscale ζfresh→
    βe+3*max ηCap ellCap≤βe₀→βh+2*ellCap≤βh₀→ν+ηCap+4*p≤rate→
    OrdinaryWheelLikelySeparateCostsCertificate Q F H X T Z W 3
      (rate*Fintype.card (V⊕U)) cover :=by
  obtain ⟨n₀,Nclean,hafter⟩:=hfixed b₀ L hL
  obtain ⟨Nreserve,Ninner,Nsafe,hcover⟩:=hafter eps heps
  let M:=max 64 (max (4*n₀) (max (4*Nreserve) (max Nclean (max Ninner Nsafe))))
  refine ⟨M,by dsimp [M];omega,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P Q F H π d X T Z W ξroot aLoad lam ellCap ηCap b₁ c₁ deep crossLoss
    βparent h εparent ξ ζ f binner c pR pH density tR tH tP Ledit βe₀ βh₀ δbal K γold κold bold Bold εold
    s j weight raw cover ell hM hV hroot hlam4 hξroot ha hlam hellCap hηCap hell hη href hpackcut hTX hWZ
    hT hW hQF hJv hJu inputs hub hF hLf hbal hdiv κscale rate hscaled hbudgetE hbudgetH hfinish
  obtain ⟨D,href⟩:=href
  have hs:=ordinary_triangle_root_free_local_sizes X T W n₀ Nreserve Nclean Ninner Nsafe 0 lam hlam4 hroot
    (by dsimp [M] at hM;omega) (by dsimp [M] at hM;omega) (by dsimp [M] at hM;omega)
    (by dsimp [M] at hM;omega) (by dsimp [M] at hM;omega) (by omega) (by dsimp [M] at hM;omega)
  obtain ⟨hn₀,hreserve,hclean,hsafe,_,hinner,h32,h16,hloss,_⟩:=hs
  exact hcover V U Γ Color hclean hsafe (1/16) (by norm_num) (by norm_num)
    P Q F H π d X T Z W ξroot aLoad lam ellCap ηCap b₁ c₁ deep crossLoss
    βparent h εparent ξ ζ f binner c pR pH density tR tH tP Ledit βe₀ βh₀ δbal K γold κold bold Bold εold
    s j weight raw hV hroot hξroot ha hlam hellCap hηCap hell hη D href hpackcut hTX hWZ hn₀ hreserve hloss
    hT hW hQF hinner h32 h16 hJv hJu inputs hub hF hLf hbal hdiv κscale rate _ _
    hscaled hbudgetE hbudgetH hfinish le_rfl le_rfl
end Oberwolfach
