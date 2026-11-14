module

public import Oberwolfach.CommonThinnedSpokeChanges
public import Oberwolfach.FiniteCoordinateEvents

@[expose] public section

/-! Eliminate the auxiliary coins once for the fixed family of hub pairs.
The coefficient function is shared by every pair. Each witness selector
is then held fixed during later changes of the host. -/
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

def CommonPotentialSpokeLoads (P : SimpleGraph V) (π : Equiv.Perm V) (d m : ℕ)
    (D p k sbar : ℝ) (weight : (Fin (m+1)→V)→ℝ) (η : ℝ)
    (σ : RawMarkedOutcome V U Γ Color) (H : Bool→V→U→Prop) (κ : V→Bool) (u u' : U) : Prop :=
  let Parent := MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
    (fun (_ : V) (_ : Unit)=>True) (fun _ _=>True)
  let seed := fun W : Parent=>weight W.1.val/(D*p^m*k*sbar^m)
  ∀ b v,|typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ)
    (commonThinnedSpokes H κ u u') (Sum.inr (b,v,()))-1|≤η

theorem thinnedMarked_exists_coins_probability
    (μ : ∀ e : RawWheelCoordinate V U,FiniteLaw (RawMarkedCoordinateState Γ Color e))
    (θ : ℝ) (hθ : 0≤θ) (hθ1 : θ≤1) (E : RawMarkedOutcome V U Γ Color→(V→Bool)→Prop) :
    (FiniteLaw.pi (thinnedMarkedLaw μ θ hθ hθ1)).probability
      (fun σ=>E (fun e=>σ (Sum.inl e)) (fun x=>σ (Sum.inr x)))≤
    (FiniteLaw.pi μ).probability (fun σ=>∃ κ,E σ κ) := by
  rw [← thinnedMarked_raw_projection μ θ hθ hθ1 (fun σ=>∃ κ,E σ κ)]
  apply finiteLaw_probability_mono
  intro σ hσ
  exact ⟨fun x=>σ (Sum.inr x),hσ⟩

theorem rawMarked_common_weight_witness_event
    (P : SimpleGraph V) (π : Equiv.Perm V)
    (p k : ℝ) (hp : 0<p) (hk : 0<k) (hphys : 2*p+2*k≤1) (d : ℕ) (hd : 2≤d)
    (q : U→Γ→ℝ) (hq : ∀ u a,0≤q u a) (hQ : ∀ u,∑ a,q u a≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a))
    (hnoshort : ∀ x l,0<l → l<2*d+1 → (π^l) x≠x)
    (m : ℕ) (hm : 3≤m) (g : Γ) (j : Color) (s₀ D τ A B : ℝ) (hs₀ : 0<s₀) (hB : 0<B)
    (hq₀ : ∀ u,q u g=s₀/m) (hs₀' : ∀ u,s u j=s₀)
    (weight : (Fin (m+1)→V)→ℝ)
    (hw : SuccessorSequenceWeightConditions P π (3*d) D τ A B weight)
    (hn : 0<Fintype.card V) (hDlo : (Fintype.card V:ℝ)/2≤D) (hDhi : D≤2*Fintype.card V)
    (pstar : ℝ) (hpstar : 0<pstar) (hpmin : pstar≤p) (hkmin : pstar≤k) (hsmin : pstar≤s₀*s₀/m)
    (hp1 : p≤1) (hk1 : k≤1) (hs1 : s₀*s₀/m≤1) (ε : ℝ) (hε : 0<ε) :
    let Bplus := 2*B/pstar^(2*m+1)
    let err := (Fintype.card (((V×V)⊕(V×V))⊕(Bool×V×Unit)):ℝ)*
      (2*Real.exp (-2*ε^2/((16*(d:ℝ)+14)^2*(((m:ℝ)+1)^4*Bplus/Fintype.card V)*(2*((m:ℝ)+1))*(((m:ℝ)+1)^2*Bplus))))
    1-(Fintype.card (U×U):ℝ)*err≤
    (FiniteLaw.pi (rawMarkedWheelLaw p k hp.le hk.le hphys d hd q hq hQ s hs hS)).probability
      (fun σ=>∀ u u',u≠u' → ∃ κ,CommonPotentialSpokeLoads P π d m D p k (s₀*s₀/m) weight
        (τ+ε) σ (rawMarkedPairSpokes π d σ g j) κ u u') := by
  intro Bplus err
  let μ := rawMarkedWheelLaw (V:=V) p k hp.le hk.le hphys d hd q hq hQ s hs hS
  let Good := fun a : U×U=>fun σ : RawMarkedOutcome V U Γ Color=>
    a.1≠a.2 → ∃ κ,CommonPotentialSpokeLoads P π d m D p k (s₀*s₀/m) weight
      (τ+ε) σ (rawMarkedPairSpokes π d σ g j) κ a.1 a.2
  have herr : 0≤err := by dsimp [err];positivity
  have hpair (a : U×U) : 1-err≤(FiniteLaw.pi μ).probability (Good a) := by
    by_cases ha : a.1=a.2
    · simp only [Good,ha,ne_eq,not_true_eq_false,false_implies,finiteLaw_probability_true]
      have ht := finiteLaw_probability_true (FiniteLaw.pi μ)
      linarith only [herr,ht]
    obtain ⟨hθ,hθ1,hsbar,hqbar,hsbar'⟩ := commonThinning_parameters m (by omega) s₀ hs₀
    have hh := thinnedMarkedSeed_spoke_event P π p k hp hk hphys d hd q hq hQ s hs hS hnoshort
      (1/(m:ℝ)) hθ hθ1 g j a.1 a.2 ha m hm (s₀*s₀/m) ((s₀/m)*(s₀/m)) D τ A B hB
      (by rw [hq₀,hq₀]) (by rw [hs₀',hs₀'];exact hsbar') hqbar weight hw hn hDlo hDhi
      pstar hpstar hpmin hkmin hsmin hp1 hk1 hs1 ε hε
    have hpj := thinnedMarked_exists_coins_probability μ (1/(m:ℝ)) hθ hθ1
      (fun σ κ=>CommonPotentialSpokeLoads P π d m D p k (s₀*s₀/m) weight
        (τ+ε) σ (rawMarkedPairSpokes π d σ g j) κ a.1 a.2)
    have hevent : 1-err≤(FiniteLaw.pi μ).probability (fun σ=>∃ κ,
        CommonPotentialSpokeLoads P π d m D p k (s₀*s₀/m) weight
          (τ+ε) σ (rawMarkedPairSpokes π d σ g j) κ a.1 a.2) := hh.trans hpj
    apply hevent.trans
    apply finiteLaw_probability_mono
    intro σ hσ _
    exact hσ
  have hh := finiteLaw_common_event_lower (FiniteLaw.pi μ) Finset.univ
    (fun a σ=>¬Good a σ) (fun _=>err) (by
      intro a ha
      have hc := finiteLaw_probability_compl (FiniteLaw.pi μ) (Good a)
      linarith only [hpair a,hc])
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.mem_univ,true_implies,
    not_not,Good,Prod.forall] using hh

end Oberwolfach
