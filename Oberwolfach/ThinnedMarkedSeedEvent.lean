module

public import Oberwolfach.ThinnedMarkedSeedMeans
public import Oberwolfach.SuccessorSeedBounds

@[expose] public section

/-! The common weighting's simultaneous potential-spoke estimates for a
fixed hub pair. The coefficients are supplied by the proved parent-weight
conditions and normalized before sampling. Neither root spokes nor the
root thinning coin occur in these sums. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
set_option quotPrecheck false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem thinnedMarkedSeed_spoke_event
    (P : SimpleGraph V) (π : Equiv.Perm V)
    (p k : ℝ) (hp : 0<p) (hk : 0<k) (hphys : 2*p+2*k≤1) (d : ℕ) (hd : 2≤d)
    (q : U→Γ→ℝ) (hq : ∀ u a,0≤q u a) (hQ : ∀ u,∑ a,q u a≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a))
    (hnoshort : ∀ x l,0<l → l<2*d+1 → (π^l) x≠x)
    (θ : ℝ) (hθ : 0≤θ) (hθ1 : θ≤1) (g : Γ) (j : Color) (u u' : U) (hu : u≠u')
    (m : ℕ) (hm : 3≤m) (sbar tbar D τ A B : ℝ) (hB : 0<B)
    (hqbar : q u g*q u' g=tbar) (hsbar : s u j*s u' j*θ=sbar) (ht : tbar=sbar/m)
    (weight : (Fin (m+1)→V)→ℝ)
    (hw : SuccessorSequenceWeightConditions P π (3*d) D τ A B weight)
    (hn : 0<Fintype.card V) (hDlo : (Fintype.card V:ℝ)/2≤D) (hDhi : D≤2*Fintype.card V)
    (pstar : ℝ) (hpstar : 0<pstar) (hpmin : pstar≤p) (hkmin : pstar≤k) (hsmin : pstar≤sbar)
    (hp1 : p≤1) (hk1 : k≤1) (hs1 : sbar≤1) (ε : ℝ) (hε : 0<ε) :
    let Bplus := 2*B/pstar^(2*m+1)
    let Parent := MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun (_ : V) (_ : Unit)=>True) (fun _ _=>True)
    let seed := fun W : Parent=>weight W.1.val/(D*p^m*k*sbar^m)
    1-(Fintype.card (((V×V)⊕(V×V))⊕(Bool×V×Unit)):ℝ)*
      (2*Real.exp (-2*ε^2/((16*(d:ℝ)+14)^2*(((m:ℝ)+1)^4*Bplus/Fintype.card V)*(2*((m:ℝ)+1))*(((m:ℝ)+1)^2*Bplus))))≤
    (FiniteLaw.pi (thinnedMarkedLaw (rawMarkedWheelLaw p k hp.le hk.le hphys d hd q hq hQ s hs hS) θ hθ hθ1)).probability
      (fun σ=>∀ b v,|typedMarkedPotentialLoad seed (rawMarkedPairRims P π d (fun e=>σ (Sum.inl e)))
        (thinnedMarkedSpokes π d g j u u' σ) (Sum.inr (b,v,()))-1|≤τ+ε) := by
  intro Bplus Parent seed
  have hnR : (0:ℝ)<Fintype.card V := by exact_mod_cast hn
  have hD : 0<D := by linarith
  have hsbar' : 0<sbar := hpstar.trans_le hsmin
  have hseed (W : Parent) := successor_seed_nonneg_upper hw (by omega) hn hDlo hDhi
    p k sbar pstar hpstar hpmin hkmin hsmin hp1 hk1 hs1 hB.le W.1.val
  have hh := thinnedMarkedPotentialLoad_mean_event P π p k hp.le hk.le hphys d hd q hq hQ s hs hS
    θ hθ hθ1 g j u u' m hm (fun _ _=>True) (fun _ _=>True) hn seed Bplus (by dsimp [Bplus];positivity) hseed ε hε
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ b v
  have hmean := thinnedMarkedSeed_spoke_mean P π p k hp hk hphys d hd q hq hQ s hs hS hnoshort
    θ hθ hθ1 g j u u' hu m (by omega) sbar tbar D τ A B hsbar' hD hqbar hsbar ht weight hw b v
  have hclose := (hσ (Sum.inr (b,v,()))).le
  exact (abs_sub_le _ _ _).trans ((add_le_add hclose hmean).trans_eq (by ring))

end Oberwolfach
