module

public import Oberwolfach.SingleClassBernoulliFactor
public import Oberwolfach.OrdinarySparseLocalFactor

@[expose] public section

/-! Fresh ordinary cycle factors. The parent absorbers are constructed
from common-neighbourhood lower bounds; no absorber-existence or factor
premise is supplied. Parent weights are fixed before vertex retention. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_fresh_local_factor (m:ℕ) (hm:2≤m) (γ κ b B:ℝ)
    (hγ:0<γ) (hκ:0<κ) (hb:0<b) (hB:0≤B):
    ∃ ε η ζ:ℝ,0<ε ∧ 0<η ∧ 0<ζ ∧
      ∀ (p:ℝ) (hp:0<p) (hp1:p≤1) (q:ℕ),∃ N:ℕ,
      ∀ (V:Type) [Fintype V] [DecidableEq V],N≤Fintype.card V→
      ∀ (Q F:SimpleGraph V) (T:Finset V),κ*Fintype.card V≤(T.card:ℝ)→
      (∀ v,(F.degree v:ℝ)≤ε*Fintype.card V)→
      (∀ X:Finset V,X.card≤(if m=2 then 3 else 2)→
        γ*Fintype.card V≤((common T X (fun x=>Q.neighborFinset x)).card:ℝ))→
      ∀ wt:LocalOrdinaryCycle Q F T (m+1)→ℝ,
      (∀ C,b/(Fintype.card V:ℝ)^m≤wt C ∧ wt C≤B/(Fintype.card V:ℝ)^m)→
      (∀ v∈T,|1-hypergraphWeightedDegree localOrdinaryVertices wt v|≤η)→
      1-1/(T.card:ℝ)^q≤
        (FiniteLaw.pi (fun _:V=>FiniteLaw.retentionCoin p hp.le hp1)).probability
          (fun σ=>∀ Y:Finset V,Y⊆T → (m+1)∣Y.card →
            ((((T∩bernoulliVertexSet σ)\Y).card+(Y\(T∩bernoulliVertexSet σ)).card:ℕ):ℝ)≤ζ*(p*T.card)→
            ∀ K:SimpleGraph V,(∀ v,(K.degree v:ℝ)≤ζ*(p*T.card))→
            ∃ D:Finset (LocalOrdinaryCycle Q F T (m+1)),
              ((∀ C∈D,∀ E∈D,C≠E→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices E)) ∧
                D.biUnion localOrdinaryVertices=Y) ∧
              ∀ C∈D,∀ x∈localOrdinaryVertices C,∀ y∈localOrdinaryVertices C,¬K.Adj x y):=by
  let β:=ordinaryLocalCountCoeff m γ
  have hβ:0<β:=ordinaryLocalCountCoeff_pos m γ hγ
  let α:=(β/2)^(m+2)
  have hα:0<α:=by dsimp [α];positivity
  let S:Unit→VertexAbsorberTemplate (m+1):=fun _=>pairedAbsorberTemplate (m+1)
  obtain ⟨η,ζ,hη,hζ,hfresh⟩:=single_class_bernoulli_factor (m+1) ((m+1)^(m+1))
    (by omega) S α (b*κ^m) B hα (by positivity) hB
  let ε:=γ/(4*(m+3:ℝ))
  have hε:0<ε:=by dsimp [ε];positivity
  obtain ⟨Na,hNa⟩:=paired_absorber_order_threshold m β hβ
  refine ⟨ε,η,ζ,hε,hη,hζ,?_⟩
  intro p hp hp1 q
  obtain ⟨Nf,hNf⟩:=hfresh p hp hp1 q
  obtain ⟨N₁,hN₁⟩:=exists_nat_gt (max (4*(m+3:ℝ)/γ) ((Nf:ℝ)/κ))
  refine ⟨max Na (max N₁ 1),?_⟩
  intro V _ _ hn Q F T hsize hF hcommon wt hw herr
  let n:ℝ:=Fintype.card V
  have hnpos:0<n:=by dsimp [n];exact_mod_cast (show 0<Fintype.card V by omega)
  have hNn:(N₁:ℝ)≤n:=by dsimp [n];exact_mod_cast (show N₁≤Fintype.card V by omega)
  have htpos:(0:ℝ)<T.card:=(mul_pos hκ hnpos).trans_le hsize
  have htn:(T.card:ℝ)≤n:=by dsimp [n];exact_mod_cast Finset.card_le_univ T
  have hlarge:4*(m+3:ℝ)≤γ*n:=by
    have hh:=(le_max_left (4*(m+3:ℝ)/γ) _).trans (hN₁.le.trans hNn)
    nlinarith only [(div_le_iff₀ hγ).mp hh]
  have hbudget:(m+3:ℝ)*(ε*n+1)≤γ/2*n:=by
    have he:(m+3:ℝ)*ε=γ/4:=by dsimp [ε];field_simp
    nlinarith only [congrArg (fun z:ℝ=>z*n) he,hlarge]
  have hNt:Nf≤T.card:=by
    have hh:=(le_max_right (4*(m+3:ℝ)/γ) ((Nf:ℝ)/κ)).trans (hN₁.le.trans hNn)
    have hh':(Nf:ℝ)≤κ*n:=by nlinarith only [(div_le_iff₀ hκ).mp hh]
    exact_mod_cast hh'.trans hsize
  apply hNf V (LocalOrdinaryCycle Q F T (m+1)) T hNt localOrdinaryVertices wt
    (fun C v hv=>C.property.1 v (Set.mem_toFinset.mp hv)) localOrdinaryVertices_card
    (local_ordinary_multiplicity Q F T)
    (fun C=>by simpa only [Nat.add_sub_cancel] using
      hub_factor_weight_scale m n T.card κ b B (wt C) hnpos htpos hκ hb.le hB htn hsize (hw C)) herr
  intro X hXT hXr
  let e:Fin (m+1)≃X:=Fintype.equivOfCardEq (by simp only [Fintype.card_fin,Fintype.card_coe,hXr])
  let x:Fin (m+1)→V:=fun i=>(e i).val
  have hx:Function.Injective x:=by intro i j h;exact e.injective (Subtype.ext h)
  have hxT (i:Fin (m+1)):x i∈T:=hXT (e i).property
  have hxX:Finset.univ.image x=X:=by
    ext v
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨i,rfl⟩;exact (e i).property
    · intro hv;obtain ⟨i,hi⟩:=e.surjective ⟨v,hv⟩;exact ⟨i,congrArg Subtype.val hi⟩
  have habs:=ordinary_local_paired_absorber_count Q F T hm γ (ε*n) hγ (by positivity)
    hF hcommon hbudget (hNa _ (by omega)).1 (hNa _ (by omega)).2 x hx hxT
  rw [hxX] at habs
  have hscale:α*(T.card:ℝ)^((m+1)*(m+1))≤α*n^((m+1)*(m+1)):=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ htpos.le htn _) hα.le
  let f:LabelledCycleRecord localOrdinaryVertices (pairedAbsorberTemplate (m+1)).val X→
      LabelledAbsorberFamily (localOrdinaryVertices (Q:=Q) (F:=F) (T:=T) (r:=m+1)) S X:=fun D=>⟨(),D⟩
  have hf:Function.Injective f:=by intro D E h;exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
  exact (hscale.trans habs).trans (by exact_mod_cast Fintype.card_le_of_injective f hf)

end Oberwolfach
