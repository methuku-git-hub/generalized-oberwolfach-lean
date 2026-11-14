module

public import Oberwolfach.MarkedProtectedActiveSeedWitness
public import Oberwolfach.FixedWeightOrderBounds

@[expose] public section

/-! The active seed uses the original coefficient function and original
normalization. Only the two order bounds and the error allowance change. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U VA UA Γ Color:Type} [Fintype VA] [Fintype UA] [LinearOrder VA] [DecidableEq UA]
  [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U]

theorem marked_active_seed_from_scale
    (f:VA↪oV) (i:UA↪U) (ρ:Equiv.Perm VA)
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (hm:3≤m) (hn:0<Fintype.card V)
    (hu:Fintype.card U≤Fintype.card V) (D τ A B p k s₀ pstar eta kappa eta0:ℝ)
    (hDlo:(Fintype.card V:ℝ)/2≤D) (hDhi:D≤2*Fintype.card V)
    (hpstar:0<pstar) (hp:pstar≤p) (hk:pstar≤k) (hs:pstar≤s₀)
    (hp1:p≤1) (hk1:k≤1) (hs1:s₀≤1) (hA:0≤A) (hB:0≤B)
    (heta:0≤eta) (hetaK:eta≤kappa) (hkappa:0≤kappa)
    (hbudget:(1+2*((m:ℝ)+1)^3*(2*B/pstar^(2*m+1))+
      66*((m:ℝ)+1)^4*(2*B/pstar^(2*m+1)))*kappa≤eta0)
    (weight:(Fin (m+1)→V)→ℝ) (hw:SuccessorSequenceWeightConditions P π (3*d) D τ A B weight)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color)
    (hq:∀ u,0<q u g) (hS:∀ u,0<s u j)
    (hload:
      let seed:=fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
        (fun (_:V) (_:U)=>True) (fun _ _=>True)=>weight W.1.val/(D*p^m*k*s₀^m)
      ∀ root,rawMarkedWheelMarginal P π d p k q s g j root≠0→
        |typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) H root-1|≤eta)
    (T:Finset V) (Z:Finset U) (hT:∀ x,π x∈T↔x∈T)
    (hf:∀ x,f (ρ x)=π (f x))
    (hfX:Finset.univ.image f=Finset.univ\T) (hiX:Finset.univ.image i=Finset.univ\Z)
    (hsize:(Fintype.card V:ℝ)/2≤Fintype.card VA) (huA:Fintype.card UA≤Fintype.card VA)
    (hTsize:(T.card:ℝ)≤kappa*Fintype.card V) (hZsize:(Z.card:ℝ)≤kappa*Fintype.card V)
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U))
    (hrim:∀ x,((DR.comap f).degree x:ℝ)≤kappa*Fintype.card V)
    (hrow:∀ x,((DS.comap (Sum.map f i)).degree (Sum.inl x):ℝ)≤kappa*Fintype.card V)
    (hcol:∀ u,((DS.comap (Sum.map f i)).degree (Sum.inr u):ℝ)≤kappa*Fintype.card V):
    let σA:=rawMarkedRestrictPair f i (rawMarkedDeleteRims σ DR.edgeFinset)
    let HA:=fun j x u=>markedDeletePhysicalSpokes H DS j (f x) (i u)
    let E:=MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σA (Sum.inl e)) false
    let K:=MarkedSampleArc (P.comap f) ρ (3*d) (fun e=>σA (Sum.inl e)) true
    let ψ:=fun W:MarkedWheel (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) m ρ (3*d) (HA false) (HA true)=>weight (f∘W.1.val)/(D*p^m*k*s₀^m);
    (∀ e,|markedWheelRimLoad ψ e-1|≤eta0)∧
    (∀ j v u,|markedSpokeResidual ψ j v u|≤eta0)∧
    (∀ W,((A/2)/2^m)/(Fintype.card VA:ℝ)^m≤ψ W∧
      ψ W≤(2*B/pstar^(2*m+1))/(Fintype.card VA:ℝ)^m):=by
  intro σA HA E K ψ
  have hn0:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
  have hnA0:(0:ℝ)<Fintype.card VA:=lt_of_lt_of_le (by positivity) hsize
  have hnA:0<Fintype.card VA:=by exact_mod_cast hnA0
  let C:=2*B/pstar^(2*m+1)
  have hC:0≤C:=by dsimp [C];positivity
  let error:=eta+((T.card:ℝ)+Z.card)*((m:ℝ)+1)^3*C/Fintype.card V+
    11*((m:ℝ)+1)^4*C*(2*(kappa*Fintype.card V)+kappa*Fintype.card V)/Fintype.card VA
  have hrat:((T.card:ℝ)+Z.card)/Fintype.card V≤2*kappa:=by
    apply (div_le_iff₀ hn0).mpr
    linarith only [hTsize,hZsize]
  have hdel:(2*(kappa*Fintype.card V)+kappa*Fintype.card V)/(Fintype.card VA:ℝ)≤6*kappa:=by
    apply (div_le_iff₀ hnA0).mpr
    have hh:=mul_le_mul_of_nonneg_left hsize hkappa
    nlinarith only [hh]
  have ha:=mul_le_mul_of_nonneg_right hrat (show 0≤((m:ℝ)+1)^3*C by positivity)
  have hb:=mul_le_mul_of_nonneg_left hdel (show 0≤11*((m:ℝ)+1)^4*C by positivity)
  have ha':((T.card:ℝ)+Z.card)*((m:ℝ)+1)^3*C/Fintype.card V≤2*kappa*(((m:ℝ)+1)^3*C):=by
    convert ha using 1 <;> ring
  have hb':11*((m:ℝ)+1)^4*C*(2*(kappa*Fintype.card V)+kappa*Fintype.card V)/Fintype.card VA≤
      11*((m:ℝ)+1)^4*C*(6*kappa):=by
    convert hb using 1 <;> ring
  have herr:error≤eta0:=by
    change (1+2*((m:ℝ)+1)^3*C+66*((m:ℝ)+1)^4*C)*kappa≤eta0 at hbudget
    dsimp only [error]
    nlinarith only [hetaK,ha',hb',hbudget]
  obtain ⟨hR,hS',hbounds⟩:=marked_protected_active_seed_witness f i ρ P π d m hm hn hu
    D τ A B p k s₀ pstar eta hDlo hDhi hpstar hp hk hs hp1 hk1 hs1 hA hB heta
    weight hw σ H q s g j hq hS hload T Z hT hf hfX hiX hnA huA DR DS
    (kappa*Fintype.card V) (kappa*Fintype.card V) (by positivity) (by positivity) hrim hrow hcol
  refine ⟨fun e=>(hR e).trans herr,fun j v u=>(hS' j v u).trans herr,?_⟩
  intro W
  exact fixed_weight_order_bounds (Fintype.card V) (Fintype.card VA) (A/2) C (ψ W) m hnA0
    (Nat.cast_le.mpr (Fintype.card_le_of_injective f f.injective)) (by linarith only [hsize])
    (by positivity) hC (hbounds W)

end Oberwolfach
