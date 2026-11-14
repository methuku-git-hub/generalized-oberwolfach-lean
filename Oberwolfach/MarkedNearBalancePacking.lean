module

public import Oberwolfach.MarkedSmallDeletionPacking
public import Oberwolfach.SparseTypedHostCorrection

@[expose] public section

/-! Near-balance marked wheel packing. The balancing deletion is constructed
inside the supplied allowed subgraphs. The same parent weighting and profiles
are used throughout, and one matching has both leftover degree bounds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_near_balance_wheel_packing (α p₀ : ℝ)
    (hα : 0<α) (hαmax : α≤1) (hp₀ : 0<p₀) (hp₀max : p₀≤1/2) :
    ∃ c₀ : ℕ,∀ k : ℕ,c₀≤k+2 → ∀ β L bminus bplus ω h δ : ℝ,
    0<β → 1≤L → 0<bminus → 0<bplus → 0<ω → 0<h → 0<δ → δ<1/4 →
    ∃ ε η₀ δ₀ : ℝ,0<ε ∧ 0<η₀ ∧ 0<δ₀ ∧
    ∀ γ : ℝ,0<γ → ∃ ηbal : ℝ,0<ηbal ∧ ∀ b : ℕ,∃ n₀ : ℕ,
    ∀ η : ℝ,0≤η → η≤ηbal →
    ∀ (V E K U : Type)
      [Fintype V] [Fintype E] [Fintype K] [Fintype U] [DecidableEq V] [DecidableEq U],
    ∀ (tail head : E → V) (ktail khead : K → V) (π : Equiv.Perm V),
    Function.Injective (markedPhysicalEdge tail head ktail khead π) →
    ∀ (p D : ℝ),p₀≤p → p≤1/2 → n₀≤Fintype.card V →
    (Fintype.card V:ℝ)/2≤D → D≤2*Fintype.card V →
    (∀ x,|occurrenceDegree tail x-p*D|≤ε*Fintype.card V) →
    (∀ x,|occurrenceDegree head x-p*D|≤ε*Fintype.card V) →
    (∀ x,|occurrenceDegree ktail x-p*D/(k+1:ℝ)|≤ε*Fintype.card V) →
    (∀ x,|occurrenceDegree khead x-p*D/(k+1:ℝ)|≤ε*Fintype.card V) →
    (∀ x y,x≠y → 2*α*p^2*Fintype.card V≤
      ((Finset.univ.filter (fun z => (∃ e,tail e=x ∧ head e=z) ∧ (∃ e,tail e=z ∧ head e=y))).card:ℝ)) →
    (∀ S T : Finset V,(1-2*min (α/16) (p/128))*Fintype.card V<(S.card:ℝ)+T.card →
      2*(α*p/16)*Fintype.card V*min (S.card:ℝ) T.card≤
      ((Finset.univ.filter (fun e => tail e∈S ∧ head e∈T)).card:ℝ)) →
    ∀ H₀ Hₖ : V → U → Prop,
    (∀ v u,¬(H₀ v u ∧ Hₖ v u)) →
    (∀ C' : MarkedCycleTuple tail head ktail khead (k+1) π b,
      2*β*Fintype.card V≤(Fintype.card {u // MarkedHubCompatible H₀ Hₖ C'.val u}:ℝ)) →
    ω*Fintype.card V≤Fintype.card U → Fintype.card U≤Fintype.card V →
    ∀ (ps qs : Bool → U → ℝ) (δsp Dexc : ℝ),
    (∀ j,SparseIntersectionData (if j then Hₖ else H₀) (ps j) (qs j) L δsp Dexc) →
    δsp+Dexc/(Fintype.card V:ℝ)+1/(Fintype.card U:ℝ)≤δ₀ →
    ∀ i : Bool → Fin (k+2),(∀ j,markedPositionType (i j)=j) →
    (∀ u u' : U,u≠u' → 2*β*(Fintype.card V:ℝ)^(k+2)≤
      (Fintype.card (CommonMarkedCycle tail head ktail khead (k+1) π b H₀ Hₖ u u'):ℝ)) →
    (∀ j,∀ Q : BipartiteFourCycle (if j then Hₖ else H₀),
      2*β*(Fintype.card V:ℝ)^(k+1)≤
      (Fintype.card (CanonicalCommonMarkedPath tail head ktail khead (k+1) π b H₀ Hₖ (i j)
        Q.val.1.1 Q.val.1.2 Q.val.2.1 Q.val.2.2):ℝ)) →
    ∀ ψ : MarkedWheel tail head ktail khead (k+1) π b H₀ Hₖ → ℝ,
    (∀ e,|markedWheelRimLoad ψ e-1|≤η₀) →
    (∀ j v u,|markedSpokeResidual ψ j v u|≤η₀) →
    (∀ W,bminus/(Fintype.card V:ℝ)^(k+1)≤ψ W ∧ ψ W≤bplus/(Fintype.card V:ℝ)^(k+1)) →
    ∀ (A₀ Aₖ : V → V → ℕ) (T₀ Tₖ : V → U → ℕ),
    (∀ x y,A₀ x y≤occurrenceMultiplicity tail head x y) →
    (∀ x y,Aₖ x y≤occurrenceMultiplicity ktail khead x y) →
    (∀ v u,T₀ v u≤relationMultiplicity H₀ v u) →
    (∀ v u,Tₖ v u≤relationMultiplicity Hₖ v u) →
    (∀ v,|occurrenceDegree (Sum.elim tail ktail) v-
      (∑ u,if H₀ v u then (1:ℝ) else 0)-(∑ u,if Hₖ v u then (1:ℝ) else 0)|≤η*Fintype.card V) →
    (∀ v,|occurrenceDegree (Sum.elim head khead) v-
      (∑ u,if H₀ v u then (1:ℝ) else 0)-(∑ u,if Hₖ v u then (1:ℝ) else 0)|≤η*Fintype.card V) →
    (∀ v,|occurrenceDegree khead v-(∑ u,if Hₖ v u then (1:ℝ) else 0)|≤η*Fintype.card V) →
    (∀ u,|(∑ v,if H₀ v u then (1:ℝ) else 0)-(k+1:ℝ)*(∑ v,if Hₖ v u then (1:ℝ) else 0)|≤η*Fintype.card V) →
    BipartiteLargeCut A₀ δ h → BipartiteLargeCut Aₖ δ h →
    BipartiteLargeCut T₀ δ h → BipartiteLargeCut Tₖ δ h →
    ∃ M : Finset (MarkedWheel tail head ktail khead (k+1) π b H₀ Hₖ),
      (∀ W∈M,∀ Z∈M,W≠Z → Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z)) ∧
      (∀ x : V⊕U,((markedIncidentEdges tail head ktail khead π H₀ Hₖ false x \
        M.biUnion markedActiveResources).card : ℝ)≤γ*Fintype.card V) ∧
      (∀ x : V⊕U,((markedPhysicalIncidentEdges tail head ktail khead π H₀ Hₖ x \
        M.biUnion markedWheelPhysicalResources).card : ℝ)≤γ*Fintype.card V) := by
  obtain ⟨c₀,hc₀⟩ := marked_small_deletion_packing α p₀ hα hαmax hp₀ hp₀max
  refine ⟨max c₀ 4,?_⟩
  intro k hk β L bminus bplus ω h δ hβ hL hbm hbp hω hh hδ hδsmall
  have hkm : 1≤k+1 := by omega
  let c : ℝ := (k:ℝ)+2
  have hc : 0<c := by dsimp only [c];positivity
  obtain ⟨ε,η₀,δ₀,hε,hη₀,hδ₀,hpacking⟩ := hc₀ k ((le_max_left _ _).trans hk)
    β L bminus bplus ω hβ hL hbm hbp hω
  refine ⟨ε,η₀,δ₀,hε,hη₀,hδ₀,?_⟩
  intro γ hγ
  obtain ⟨σ,hσ,hpack⟩ := hpacking γ hγ
  let ξ := min (σ/(2*c)) (h/(200*c))
  have hξ : 0<ξ := by dsimp only [ξ];positivity
  have hξh : ((k+1:ℕ):ℝ)+1=c := by dsimp only [c];push_cast;ring
  have hξcut : (((k+1:ℕ):ℝ)+1)*ξ≤h/100 := by
    rw [hξh]
    have hh' := (le_div_iff₀ (by positivity : 0<200*c)).mp (min_le_right (σ/(2*c)) (h/(200*c)))
    have hnon := mul_nonneg hc.le hξ.le
    dsimp only [ξ] at hnon ⊢
    nlinarith only [hh',hnon]
  obtain ⟨ηbal,hηbal,Ncorr,hcorr⟩ := sparse_typed_host_correction (k+1) hkm ω h δ ξ
    hω hδ hδsmall hξ hξcut
  refine ⟨ηbal,hηbal,?_⟩
  intro b
  obtain ⟨Npack,hP⟩ := hpack b
  refine ⟨max Ncorr Npack,?_⟩
  intro η hη hηsmall V E K U _ _ _ _ _ _ tail head ktail khead π hphys p D hp hpmax hn hDlo hDhi
    hdo hdi hdko hdki htwo hcut H₀ Hₖ hdisj hhub hωn huV ps qs δsp Dexc hdata hsmall i hipos
    hcommon hpaths ψ hRerr hSerr hψ A₀ Aₖ T₀ Tₖ hA0 hAK hT0 hTK hbp0 hbm0 hbk hbw hcut0 hcutK hcutH0 hcutHK
  obtain ⟨hinj,hkinj⟩ := markedPhysicalEdge_endpoint_injections tail head ktail khead π hphys
  obtain ⟨J₀,Jₖ,L₀,Lₖ,hJ0,hJK,hL0,hLK,hbalance,hV,hU⟩ := hcorr η hη hηsmall V U E K
    ((le_max_left _ _).trans hn) hωn huV tail head ktail khead hinj hkinj H₀ Hₖ A₀ Aₖ T₀ Tₖ
    hA0 hAK hT0 hTK hbp0 hbm0 hbk (by simpa only [Nat.cast_add,Nat.cast_one] using hbw)
    hcut0 hcutK hcutH0 hcutHK
  have hbound : 2*((((k+1:ℕ):ℝ))+1)*ξ*Fintype.card V≤σ*Fintype.card V := by
    rw [hξh]
    have hs := (le_div_iff₀ (by positivity : 0<2*c)).mp (min_le_left (σ/(2*c)) (h/(200*c)))
    have ht := mul_le_mul_of_nonneg_right hs (by positivity : 0≤(Fintype.card V:ℝ))
    dsimp only [ξ]
    nlinarith only [ht]
  exact hP V E K U tail head ktail khead π hphys p D hp hpmax ((le_max_right _ _).trans hn)
    hDlo hDhi hdo hdi hdko hdki htwo hcut H₀ Hₖ hdisj hhub hωn huV ps qs δsp Dexc hdata hsmall
    i hipos hcommon hpaths ψ hRerr hSerr hψ J₀ Jₖ L₀ Lₖ
    (fun x y=>(hJ0 x y).trans (hA0 x y)) (fun x y=>(hJK x y).trans (hAK x y))
    (fun v u=>(hL0 v u).trans (hT0 v u)) (fun v u=>(hLK v u).trans (hTK v u)) hbalance
    (fun v=>⟨(hV v).1.trans hbound,(hV v).2.1.trans hbound,(hV v).2.2.1.trans hbound,
      (hV v).2.2.2.1.trans hbound,(hV v).2.2.2.2.1.trans hbound,(hV v).2.2.2.2.2.trans hbound⟩)
    (fun u=>⟨(hU u).1.trans hbound,(hU u).2.trans hbound⟩)

end Oberwolfach
