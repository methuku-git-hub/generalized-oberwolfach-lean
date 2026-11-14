module

public import Oberwolfach.MarkedActiveReferenceGeometry
public import Oberwolfach.MarkedProtectedActiveOrdinaryCut
public import Oberwolfach.MarkedProtectedActiveFourCuts

@[expose] public section

/-! All active cut inputs follow simultaneously from the original cut
family, using one original-order deletion allowance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U A B Γ Color:Type} [Fintype V] [Fintype U] [Fintype A] [Fintype B]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder A] [DecidableEq U] [DecidableEq B]

theorem marked_active_reference_cuts_from_scale
    (f:A↪oV) (g:B↪U) (π:Equiv.Perm V) (ρ:Equiv.Perm A)
    (hf:∀ x,f (ρ x)=π (f x)) (P:SimpleGraph V) (d:ℕ) (hn:0<Fintype.card V)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop) (a:Γ) (c:Color)
    (gamma omega kstar tstar p k kappa:ℝ)
    (hg:0<gamma) (ho:0<omega) (ho1:omega≤1) (hks:0<kstar) (hts:0<tstar)
    (hp:kstar≤p) (hk:kstar≤k) (hp1:p≤1) (hts1:tstar≤1) (hκ:0≤kappa)
    (hκ4:kappa≤1/4) (hκO:kappa≤omega/2)
    (hubs:omega*Fintype.card V≤(Fintype.card U:ℝ))
    (hRsize:(Fintype.card V:ℝ)-Fintype.card A≤kappa*Fintype.card V)
    (hUsize:(Fintype.card U:ℝ)-Fintype.card B≤kappa*Fintype.card V)
    (hOrd:kappa≤min ((gamma/8)/16) (p/128)) (hOrdLoss:2*kappa≤gamma*p/8)
    (hFour:kappa≤(min (min gamma kstar) tstar/256)*omega/2)
    (hFourLoss:(1+2/omega)*kappa≤14*(min (gamma*kstar) tstar/128))
    (hcuts:MarkedReferenceCutFamilies P π d a c gamma p k tstar σ)
    (hrowOld:∀ mark x,(∑ u,if ¬(rawMarkedPairSpokes π d σ a c mark x u↔H mark x u) then (1:ℝ) else 0)≤kappa*Fintype.card U)
    (hcolOld:∀ mark u,(∑ x,if ¬(rawMarkedPairSpokes π d σ a c mark x u↔H mark x u) then (1:ℝ) else 0)≤kappa*Fintype.card V)
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U))
    (hrim:∀ x,((DR.comap f).degree x:ℝ)≤kappa*Fintype.card V)
    (hrow:∀ x,((DS.comap (Sum.map f g)).degree (Sum.inl x):ℝ)≤kappa*Fintype.card V)
    (hcol:∀ u,((DS.comap (Sum.map f g)).degree (Sum.inr u):ℝ)≤kappa*Fintype.card V):
    let delta:=min (min gamma kstar) tstar/256
    let hcut:=min (gamma*kstar) tstar/128
    let σA:=rawMarkedRestrictPair f g (rawMarkedDeleteRims σ DR.edgeFinset)
    let HA:=fun b x u=>markedDeletePhysicalSpokes H DS b (f x) (g u);
    (∀ S T:Finset A,(1-2*min ((gamma/8)/16) (p/128))*Fintype.card A<(S.card:ℝ)+T.card→
      4*((gamma/8)*p/16)*Fintype.card A*min (S.card:ℝ) T.card≤
      ((Finset.univ.filter (fun e:MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σA (Sum.inl e)) false=>
        e.val.1∈S∧e.val.2∈T)).card:ℝ))∧
    (∀ mark,BipartiteLargeCut
      (occurrenceMultiplicity (fun e:MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σA (Sum.inl e)) mark=>e.val.1)
        (fun e=>e.val.2)) (delta/2) (2*hcut))∧
    (∀ mark,BipartiteLargeCut (relationMultiplicity (HA mark)) (delta/2) (2*hcut)):=by
  intro delta hcut σA HA
  have hn0:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
  have hd:0≤delta:=by dsimp [delta];positivity
  obtain ⟨hA,hAhalf,hBhalf,hA0,hB0,hAfour,hBfour,hAR,hBR⟩:=marked_active_reference_geometry_from_scale
    (Fintype.card V) (Fintype.card U) (Fintype.card A) (Fintype.card B) omega kappa delta
    hn0 ho ho1 hκ hκ4 hκO hd hFour hRsize hUsize hubs
  have hnA:0<Fintype.card A:=by exact_mod_cast hA0
  have hnB:0<Fintype.card B:=by exact_mod_cast hB0
  have hArim:∀ x,((DR.comap f).degree x:ℝ)≤(2*kappa)*Fintype.card A:=by
    intro x
    apply (hrim x).trans
    have h:=mul_le_mul_of_nonneg_left hAhalf hκ
    nlinarith only [h]
  have hAord:(1-min ((gamma/8)/16) (p/128))*Fintype.card V≤(Fintype.card A:ℝ):=by
    have h:=mul_le_mul_of_nonneg_right hOrd hn0.le
    nlinarith only [hRsize,h]
  have hordinary:=marked_protected_active_ordinary_cut f g π ρ hf P d hnA σ DR a c
    gamma p k tstar (2*kappa) hg.le (hks.le.trans hp) hp1 (by positivity) hOrdLoss hcuts hAord hArim
  have hremaining:kappa+2*kappa/omega≤14*hcut:=by
    change (1+2/omega)*kappa≤14*hcut at hFourLoss
    convert hFourLoss using 1 <;> ring
  obtain ⟨hR,hS⟩:=marked_protected_active_four_cuts f g π ρ hf P d hnA hnB σ H a c
    gamma kstar tstar p k kappa (2*kappa/omega) hg hks hts hp hk hts1 hκ (by positivity)
    hcuts hrowOld hcolOld DR DS (fun x=>(hrim x).trans hAR)
    (fun x=>(hrow x).trans hBR) (fun u=>(hcol u).trans hAR) hAfour hBfour hremaining
  exact ⟨hordinary,hR,hS⟩

end Oberwolfach
