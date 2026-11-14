module

public import Oberwolfach.OrdinaryFineCoverNormalizedRatesGeneralLoad
public import Oberwolfach.OrdinaryRootCoverSharpReferenceExists

@[expose] public section
/-! Normalize a general separate-load sharp reference without replacing its
actual root-cover witness or changing the protected-boundary cost. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_general_sharp_reference_normalized_rates
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [LinearOrder U]
    (P Q F:SimpleGraph V) (H:V→U→Prop) (I T:Finset V) (J W:Finset U) (m loadK k:ℕ) (hm:3≤m+1)
    (ξroot κ lam ellCap finishCap bin cin deep loss α ω βparent β b B h δ εparent εstar η ξ ζ p ε f binner c:ℝ)
    (hnV:0<Fintype.card V) (hroot:(T.card:ℝ)+W.card≤lam*Fintype.card V)
    (hξ:0≤ξroot) (hκ:0≤κ) (hlam:0≤lam)
    (hell:max (18*κ+3*((loadK+1)*lam)) ((3*κ+lam)*((m:ℝ)+1))≤ellCap)
    (hcover:10*ξroot≤finishCap):
    let cover:=10*ξroot*I.card;
    let ell:=max (18*κ*Fintype.card V+3*((W.card:ℝ)+((loadK:ℝ)+1)*T.card))
      (3*κ*Fintype.card V*((m:ℝ)+1)+(T.card:ℝ)*((m:ℝ)+1));
    OrdinaryRootCoverSharpReferenceExists P Q F H I T J W (m+1) k hm
      cover ell bin cin deep loss α ω βparent β b B h δ εparent εstar η ξ ζ p ε f binner c→
    ∃ηrate ellrate:ℝ,0≤ηrate ∧ ηrate≤finishCap ∧ 0≤ellrate ∧ ellrate≤ellCap ∧
      ηrate*Fintype.card (V⊕U)=cover ∧
      OrdinaryRootCoverSharpReferenceExists P Q F H I T J W (m+1) k hm
        (ηrate*Fintype.card (V⊕U)) (ellrate*Fintype.card (V⊕U))
        bin cin deep loss α ω βparent β b B h δ εparent εstar η ξ ζ p ε f binner c :=by
  intro cover ell href
  have hdata:=ordinary_fine_cover_normalized_rates_general_load m loadK I T W ξroot κ lam hnV hξ hκ hlam hroot
  let N:ℝ:=Fintype.card (V⊕U)
  let ηrate:=cover/N
  let ellrate:=ell/N
  have hdata':0<N ∧ 0≤ηrate ∧ 0≤ellrate ∧ ηrate*N=cover ∧ ellrate*N=ell ∧
      ηrate≤10*ξroot ∧ ellrate≤max (18*κ+3*((loadK+1)*lam)) ((3*κ+lam)*((m:ℝ)+1)):=by
    convert hdata using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  refine ⟨ηrate,ellrate,hdata'.2.1,hdata'.2.2.2.2.2.1.trans hcover,hdata'.2.2.1,
    hdata'.2.2.2.2.2.2.trans hell,hdata'.2.2.2.1,?_⟩
  rw [hdata'.2.2.2.1,hdata'.2.2.2.2.1]
  exact href
end Oberwolfach
