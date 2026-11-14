module

public import Oberwolfach.MarkedVortexInitialCommonTransfer
public import Oberwolfach.MarkedVortexCorrectedRecordConsequences

@[expose] public section
/-! Feed the selected, more precise parent record directly into the common
initial-field transfer on the same sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_vortex_initial_common_from_parent_record
    (r:ℕ) (κ α ω plo klo:ℝ)
    (hκ:0<κ) (hα:0<α) (hω:0<ω) (hp:0<plo) (hk:0<klo):
    ∃cap:ℝ,0<cap ∧ ∀ζ:ℝ,0≤ζ→ζ≤cap→
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [Nonempty V] [DecidableEq U],
    ∀ (h k₀ d:ℕ) (ρ₀ sstar tstar kstar:ℝ)
    (εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow:ℝ)
    (size a₀ b₀ e₀ f₀:ℕ) (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hpres:∀i v,π v∈Q.extendedVertices i↔v∈Q.extendedVertices i)
    (L:ℕ) (s₀ p kval:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color)
    (weightParent:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
    (weight:∀i,(Fin (r+4+1)→↥((Finset.univ\markedVortexInnerVertices Q i):Finset (markedVortexVertexType Q i)))→ℝ)
    (σold σglobal:RawMarkedOutcome V U Γ Color) (Hold Hglobal:Bool→V→U→Prop)
    (βA βrec thetaDeep etaBal x eta deltaI hIcut:ℝ)
    (hpEq:p=initialIndexDensity U D*s₀/2) (hkEq:kval=p/((r+4:ℕ):ℝ))
    (hOld:MarkedVortexCorrectedRecordConsequences r h k₀ d α ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σold Hold βA βrec (κ/2) thetaDeep etaBal x eta deltaI hIcut)
    (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U))
    (hn:0<Fintype.card V) (hU:ω*Fintype.card V≤(Fintype.card U:ℝ))
    (hinterval:∀e,σold (Sum.inr e)=σglobal (Sum.inr e))
    (hR:∀e,¬(rawMarkedPairRims G π d σold e↔rawMarkedPairRims G π d σglobal e)→markedPairPhysical π e∈FR.edgeFinset)
    (hS:∀b v u,¬(Hold b v u↔Hglobal b v u)→FS.Adj (Sum.inl v) (Sum.inr u))
    (hFR:∀v,(FR.degree v:ℝ)≤ζ*Fintype.card V) (hFS:∀z,(FS.degree z:ℝ)≤ζ*Fintype.card V)
    (htypes:∀v u,¬(Hold false v u∧Hold true v u))
    (hplo:plo≤p) (hklo:klo≤kval),
    let W:=markedVortexVertexType Q 0
    let Z:=markedVortexHubType Q 0
    let f:=markedVortexVertexEmbedding Q 0
    let g:=markedVortexHubEmbedding Q 0
    let ρ:=markedVortexPermutation Q π hpres 0
    let P:=G.comap f
    let σ:=rawMarkedRestrictPair f g σglobal
    let H:=fun b v u=>Hglobal b (f v) (g u)
    let c:ℝ:=(r+4:ℕ)
    let t:=s₀/c
    let Dload:=2*(Fintype.card Z:ℝ)/initialIndexDensity U D;
    MarkedReferenceStatistics P ρ d a j Dload (κ/4) κ (α/16) p kval (c*t) t σ ∧
    MarkedReferenceCutFamilies P ρ d a j (α/16) p kval t σ ∧
    MarkedCommonConfigurationsWithSpokes r P ρ d βA (κ/4) σ H ∧
    MarkedRowsWithSpokes P ρ d (r+12) Finset.univ p kval (fun u=>q (g u)) (fun u=>s (g u)) a j ((κ/4)*Fintype.card W) σ H ∧
    MarkedIndicesWithSpokes ρ d (r+12) Finset.univ (fun u=>q (g u)) (fun u=>s (g u)) a j ((κ/4)*Fintype.card W) σ H ∧
    (∀b v,(∑u,if ¬(rawMarkedPairSpokes ρ d σ a j b v u↔H b v u) then (1:ℝ) else 0)≤(κ/4)*Fintype.card Z) ∧
    (∀b u,(∑v,if ¬(rawMarkedPairSpokes ρ d σ a j b v u↔H b v u) then (1:ℝ) else 0)≤(κ/4)*Fintype.card W) :=by
  obtain ⟨cap,hcap,htransfer⟩:=marked_vortex_initial_common_transfer r κ α ω plo klo hκ hα hω hp hk
  refine ⟨cap,hcap,?_⟩
  intro ζ hζ hζcap V U Γ Color _ _ _ _ _ _ _ h k₀ d ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σold σglobal Hold Hglobal
    βA βrec thetaDeep etaBal x eta deltaI hIcut hpEq hkEq hOld FR FS hn hU hinterval hR hS hFR hFS htypes hplo hklo
    W Z f g ρ P σ H c t Dload
  have hc:(c:ℝ)≠0:=by dsimp [c];positivity
  have hct:c*t=s₀:=by dsimp [t];field_simp
  have hpRef:initialIndexDensity U D*(r+4:ℝ)*t/2=p:=by rw [hpEq,←hct]; dsimp [c]; push_cast; ring
  have hkRef:(initialIndexDensity U D*(r+4:ℝ)*t/2)/(r+4:ℝ)=kval:=by rw [hpRef,hkEq];norm_cast
  unfold MarkedVortexCorrectedRecordConsequences at hOld
  obtain ⟨hconfig,hrows,hstats,_,_,_,_,_⟩:=hOld
  obtain ⟨hcommon,_,_⟩:=hconfig 0 (Nat.zero_le L)
  obtain ⟨hrow,hindex,hrowdiff,hcoldiff⟩:=hrows 0 (Nat.zero_le L)
  obtain ⟨href,hcut⟩:=hstats 0 (Nat.zero_le L)
  have he:κ/2/4=κ/8:=by ring
  have ha:2*(α/16)=α/8:=by ring
  rw [he] at hcommon hrow hindex hrowdiff hcoldiff href
  rw [ha] at href hcut
  simp only [Nat.cast_add,Nat.cast_ofNat] at href hcut hkEq
  have hpRef':initialIndexDensity U D*(r+4:ℝ)*(s₀/(r+4:ℝ))/2=p:=by
    simpa only [t,c,Nat.cast_add,Nat.cast_ofNat] using hpRef
  rw [hpRef',←hkEq] at href hcut
  have result:=htransfer ζ hζ hζcap V U Γ Color G D m β ε Q π hpres d σold σglobal Hold Hglobal FR FS
    hn hU hinterval hR hS hFR hFS htypes a j (initialIndexDensity U D) t Dload βA (fun u=>q (g u)) (fun u=>s (g u))
    (by rw [hpRef];exact hplo) (by rw [hkRef];exact hklo)
  rw [hpRef,←hkEq] at result
  simp only [t,c,Nat.cast_add,Nat.cast_ofNat] at result ⊢
  exact result href hcut hrow hindex hcommon hrowdiff hcoldiff
end Oberwolfach
