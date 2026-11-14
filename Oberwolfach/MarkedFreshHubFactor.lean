module

public import Oberwolfach.MarkedHubFactor
public import Oberwolfach.SupportedBernoulliFactor

@[expose] public section

/-! A fresh marked factor with parent classes of arbitrary sizes. The exact
one-to-m ratio is imposed only on the final selected classes. The paired
absorber counts are derived from the actual cycle and root-omitted common
path counts. One event includes all permitted later class changes and
forbidden graphs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 10000000
noncomputable section
open scoped BigOperators
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_fresh_hub_factor (m : ℕ) (hm : 3<m+1) (β b₀ B₀ : ℝ)
    (hβ : 0<β) (hb₀ : 0<b₀) (hB₀ : 0≤B₀) :
    ∃ η ζ:ℝ,0<η ∧ 0<ζ ∧ ∀ (p:ℝ) (hp:0<p) (hp1:p≤1) (q:ℕ),∃ N:ℕ,
      ∀ (V : Bool→Type) [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]
        (A U E K : Type) [Fintype A] [DecidableEq A],N≤Fintype.card (Σ i,V i)→
      ∀ (e:(Σ i,V i)↪A) (tail head:E→A) (ktail khead:K→A)
        (π:Equiv.Perm A) (b:ℕ) (H₀ HK:A→U→Prop) (u:U),
      (∀ v,HK v u↔∃ z:V true,e ⟨true,z⟩=v)→
      (∀ v,H₀ v u↔∃ z:V false,e ⟨false,z⟩=v)→
      β*(Fintype.card A:ℝ)^(m+1)≤Fintype.card (HubMarkedCycle tail head ktail khead m π b H₀ HK u)→
      (∀ j:Bool,∀ v v':A,v≠v'→(if j then HK v u else H₀ v u)→(if j then HK v' u else H₀ v' u)→
        β*(Fintype.card A:ℝ)^m≤Fintype.card (RootFirstCommonMarkedPath tail head ktail khead m π b H₀ HK j v v' u u))→
      ∀ wt:HubMarkedCycle tail head ktail khead m π b H₀ HK u→ℝ,
      (∀ C,b₀/(Fintype.card (Σ i,V i):ℝ)^m≤wt C ∧ wt C≤B₀/(Fintype.card (Σ i,V i):ℝ)^m)→
      (∀ v,|1-hypergraphWeightedDegree (hubMarkedCycleVertices u) wt (e v)|≤η)→
      1-1/(Fintype.card (Σ i,V i):ℝ)^q≤
      (FiniteLaw.pi (fun _:A=>FiniteLaw.retentionCoin p hp.le hp1)).probability
        (fun σ=>∀ (Y:Finset (Σ i,V i)) (k:ℕ),
          (∀ i,(Finset.univ.filter (fun v:V i=>(⟨i,v⟩:Σ i,V i)∈Y)).card=twoClassProfile m i*k)→
          ((((bernoulliVertexSet (fun z=>σ (e z)))\Y).card+(Y\bernoulliVertexSet (fun z=>σ (e z))).card:ℕ):ℝ)
            ≤ζ*(p*Fintype.card (Σ i,V i))→
          ∀ F:SimpleGraph A,(∀ v,(F.degree v:ℝ)≤ζ*(p*Fintype.card (Σ i,V i)))→
          ∃ D:Finset (HubMarkedCycle tail head ktail khead m π b H₀ HK u),
            ((∀ C∈D,∀ C'∈D,C≠C'→Disjoint (hubMarkedCycleVertices u C) (hubMarkedCycleVertices u C')) ∧
              D.biUnion (hubMarkedCycleVertices u)=Y.image e) ∧
            ∀ C∈D,∀ x∈hubMarkedCycleVertices u C,∀ y∈hubMarkedCycleVertices u C,¬F.Adj x y) := by
  let α:=(β/2)^(m+2)
  have hα:0<α:=by dsimp [α];positivity
  let S:Unit→VertexAbsorberTemplate (m+1):=fun _=>pairedAbsorberTemplate (m+1)
  have ha (i:Bool):1≤twoClassProfile m i:=by cases i <;> simp [twoClassProfile] <;> omega
  obtain ⟨η,ζ,hη,hζ,hfresh⟩:=supported_bernoulli_graph_avoiding_factor (twoClassProfile m)
    (m+1) ((m+1)^(m+1)) (by omega) ha (twoClassProfile_sum m) S α b₀ B₀ hα hb₀ hB₀
  obtain ⟨Na,hNa⟩:=paired_absorber_order_threshold m β hβ
  refine ⟨η,ζ,hη,hζ,?_⟩
  intro p hp hp1 q
  obtain ⟨Nf,hNf⟩:=hfresh p hp hp1 q
  refine ⟨max Na Nf,?_⟩
  intro V _ _ A U E K _ _ hn e tail head ktail khead π b H₀ HK u hK hO hbase hpath wt hw herr
  have hcard:Fintype.card (Σ i,V i)≤Fintype.card A:=Fintype.card_le_of_injective e e.injective
  have hNn:Na≤Fintype.card A:=by omega
  let C:=HubMarkedCycle tail head ktail khead m π b H₀ HK u
  let R:C→Finset A:=hubMarkedCycleVertices u
  apply hNf V A C (by omega) e R wt
    (hubMarkedCycle_supported e u hK hO) (ambient_hubMarkedCycle_profile e u hK hO)
    (ambient_hubMarkedCycle_multiplicity u) (by simpa only [Nat.add_sub_cancel] using hw) herr
  intro ρ
  obtain ⟨x,hx,hxset,hxK,hxO⟩:=exists_twoClass_root_order ρ
  have hxhub:MarkedHubCompatible H₀ HK (fun j=>e (x j)) u:=by
    refine ⟨(hK _).mpr ((embedded_class_image_iff e true (x 0)).mpr hxK),?_⟩
    intro j
    exact (hO _).mpr ((embedded_class_image_iff e false (x j.succ)).mpr (hxO j))
  have hc:=marked_hub_paired_absorber_count hm u (fun j=>e (x j)) (e.injective.comp hx)
    hxhub β hβ hbase hpath (hNa _ hNn).1 (hNa _ hNn).2
  have hscale:α*(Fintype.card (Σ i,V i):ℝ)^((m+1)*(m+1))≤
      (β/2)^(m+2)*(Fintype.card A:ℝ)^((m+1)*(m+1)):=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr hcard) _) hα.le
  have hroot:Finset.univ.image (fun j=>e (x j))=(profileRootSet ρ).image e:=by
    rw [←hxset,Finset.image_image];rfl
  rw [hroot] at hc
  let emb:LabelledCycleRecord R (pairedAbsorberTemplate (m+1)).val ((profileRootSet ρ).image e)→
      LabelledAbsorberFamily R S ((profileRootSet ρ).image e):=fun D=>⟨(),D⟩
  have hi:Function.Injective emb:=by intro D E he;exact eq_of_heq (Sigma.mk.inj_iff.mp he).2
  exact (hscale.trans hc).trans (by exact_mod_cast Fintype.card_le_of_injective emb hi)

end Oberwolfach
