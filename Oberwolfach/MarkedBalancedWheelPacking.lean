module

public import Oberwolfach.PositiveMarkedWheelWeights
public import Oberwolfach.MarkedWheelPacking

@[expose] public section

/-! Exact marked degree identities and a positive approximate weighting give
one packing with simultaneous auxiliary and physical leftover bounds. The
weight and host error tolerances are selected before the requested leftover
tolerance, and the separation parameter is supplied afterwards. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_balanced_wheel_packing (α p₀ : ℝ)
    (hα : 0<α) (hαmax : α≤1) (hp₀ : 0<p₀) (hp₀max : p₀≤1/2) :
    ∃ c₀ : ℕ,∀ k : ℕ,c₀≤k+2 → ∀ β L bminus bplus : ℝ,0<β → 1≤L → 0<bminus → 0<bplus →
    ∃ ε η₀ δ₀ : ℝ,0<ε ∧ 0<η₀ ∧ 0<δ₀ ∧
    ∀ b : ℕ,∀ γ : ℝ,0<γ → ∃ n₀ : ℕ,
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
    (∀ x y,x≠y → α*p^2*Fintype.card V≤
      ((Finset.univ.filter (fun z => (∃ e,tail e=x ∧ head e=z) ∧ (∃ e,tail e=z ∧ head e=y))).card:ℝ)) →
    (∀ S T : Finset V,(1-2*min (α/16) (p/128))*Fintype.card V<(S.card:ℝ)+T.card →
      (α*p/16)*Fintype.card V*min (S.card:ℝ) T.card≤
      ((Finset.univ.filter (fun e => tail e∈S ∧ head e∈T)).card:ℝ)) →
    ∀ H₀ Hₖ : V → U → Prop,
    (∀ v u,¬(H₀ v u ∧ Hₖ v u)) →
    (∀ C' : MarkedCycleTuple tail head ktail khead (k+1) π b,
      β*Fintype.card V≤(Fintype.card {u // MarkedHubCompatible H₀ Hₖ C'.val u}:ℝ)) →
    (∀ v,occurrenceDegree (Sum.elim tail ktail) v=occurrenceDegree (Sum.elim head khead) v) →
    (∀ v,occurrenceDegree khead v=∑ u,if Hₖ v u then (1:ℝ) else 0) →
    (∀ v,occurrenceDegree (Sum.elim tail ktail) v=
      (∑ u,if H₀ v u then (1:ℝ) else 0)+(∑ u,if Hₖ v u then (1:ℝ) else 0)) →
    (∀ u,(∑ v,if H₀ v u then (1:ℝ) else 0)=(k+1:ℝ)*(∑ v,if Hₖ v u then (1:ℝ) else 0)) →
    0<Fintype.card U → Fintype.card U≤Fintype.card V →
    ∀ (ps qs : Bool → U → ℝ) (δsp Dexc : ℝ),
    (∀ j,SparseIntersectionData (if j then Hₖ else H₀) (ps j) (qs j) L δsp Dexc) →
    δsp+Dexc/(Fintype.card V:ℝ)+1/(Fintype.card U:ℝ)≤δ₀ →
    ∀ i : Bool → Fin (k+2),(∀ j,markedPositionType (i j)=j) →
    (∀ u u' : U,u≠u' → β*(Fintype.card V:ℝ)^(k+2)≤
      (Fintype.card (CommonMarkedCycle tail head ktail khead (k+1) π b H₀ Hₖ u u'):ℝ)) →
    (∀ j,∀ Q : BipartiteFourCycle (if j then Hₖ else H₀),
      β*(Fintype.card V:ℝ)^(k+1)≤
      (Fintype.card (MarkedReplacementPair tail head ktail khead (k+1) π b H₀ Hₖ (i j)
        Q.val.1.1 Q.val.1.2 Q.val.2.1 Q.val.2.2):ℝ)) →
    ∀ η : ℝ,0≤η → η≤η₀ →
    ∀ ψ : MarkedWheel tail head ktail khead (k+1) π b H₀ Hₖ → ℝ,
    (∀ e,|markedWheelRimLoad ψ e-1|≤η) →
    (∀ j v u,|markedSpokeResidual ψ j v u|≤η) →
    (∀ W,bminus/(Fintype.card V:ℝ)^(k+1)≤ψ W ∧ ψ W≤bplus/(Fintype.card V:ℝ)^(k+1)) →
    ∃ M : Finset (MarkedWheel tail head ktail khead (k+1) π b H₀ Hₖ),
      (∀ W∈M,∀ Z∈M,W≠Z → Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z)) ∧
      (∀ x : V⊕U,((markedIncidentEdges tail head ktail khead π H₀ Hₖ false x \
        M.biUnion markedActiveResources).card : ℝ)≤γ*Fintype.card V) ∧
      (∀ x : V⊕U,((markedPhysicalIncidentEdges tail head ktail khead π H₀ Hₖ x \
        M.biUnion markedWheelPhysicalResources).card : ℝ)≤γ*Fintype.card V) := by
  obtain ⟨c₀,hc₀⟩ := positive_marked_wheel_weights_uniform_parameters
    α p₀ hα hαmax hp₀ hp₀max
  refine ⟨max c₀ 4,?_⟩
  intro k hk β L bminus bplus hβ hL hbm hbp
  have hkm : 3≤k+1 := by omega
  obtain ⟨ε,η₀,δ₀,A,hε,hη₀,hδ₀,hA,hweights⟩ := hc₀ k ((le_max_left _ _).trans hk) β L bminus bplus hβ hL hbm hbp
  refine ⟨ε,η₀,δ₀,hε,hη₀,hδ₀,?_⟩
  intro b γ hγ
  obtain ⟨NW,hW⟩ := hweights b
  obtain ⟨NP,hP⟩ := marked_wheel_packing_bounded_hubs (k+1) hkm A γ hA hγ
  refine ⟨max NW NP,?_⟩
  intro V E K U _ _ _ _ _ _ tail head ktail khead π hphys p D hp hpmax hn hDlo hDhi
    hdo hdi hdko hdki htwo hcut H₀ Hₖ hdisj hhub hdir hK hout hcol hu huV
    ps qs δsp Dexc hdata hsmall i hipos hcommon hpaths η hη hηsmall ψ hRerr hSerr hψ
  obtain ⟨w,hwR,hwS,hwb⟩ := hW V E K U tail head ktail khead π hphys p D hp hpmax
    ((le_max_left _ _).trans hn) hDlo hDhi hdo hdi hdko hdki htwo hcut H₀ Hₖ
    hhub hdir hK hout hcol hu ps qs δsp Dexc hdata hsmall i hipos hcommon hpaths η hη hηsmall ψ hRerr hSerr hψ
  exact hP V U E K ((le_max_right _ _).trans hn) huV tail head ktail khead π b H₀ Hₖ hphys hdisj w
    (fun W=>⟨(by positivity : 0≤(bminus/2)/(Fintype.card V:ℝ)^(k+1)).trans (hwb W).1,(hwb W).2⟩) hwR
    (by
      intro j v u
      have hh := hwS j v u
      cases j <;> convert hh using 1 <;> simp only [ite_true,Bool.false_eq_true,ite_false] <;> congr!)

end Oberwolfach
