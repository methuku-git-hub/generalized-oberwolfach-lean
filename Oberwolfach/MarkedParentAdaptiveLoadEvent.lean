module

public import Oberwolfach.MarkedPackingAdaptiveVortexEvent
public import Oberwolfach.MarkedPackingZeroDeletionAnyInstance
public import Oberwolfach.RawMarkedPairRestrictionIdentity

@[expose] public section
/-! The one-level specialization of the retained adaptive packing event,
with the full vertex and hub domains and their identity embeddings. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
theorem marked_parent_adaptive_load_common_event
    (m d:ℕ) (hm:3≤m) (hd:2≤d) (B pstar ε K eta χ Q pret ζ:ℝ)
    (hB:0<B) (hpstar:0<pstar) (hε:0<ε) (hK:1≤K)
    (heta:0<eta) (heta1:eta<1) (hχ:0<χ) (hpret:0<pret) (hζ:0<ζ):
    ∃ M N:ℕ,1≤M ∧ 1≤N ∧
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [Nonempty V] [DecidableEq U],
    N≤Fintype.card V → M≤Fintype.card V → M≤Fintype.card U → Fintype.card U≤Fintype.card V →
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V),
    (∀ x l,0<l→l<2*d+1→(π^l) x≠x) →
    ∀ (D τ A:ℝ),(Fintype.card V:ℝ)/2≤D → D≤2*Fintype.card V →
    ∀ weight:(Fin (m+1)→V)→ℝ,SuccessorSequenceWeightConditions P π (3*d) D τ A B weight →
    ∀ (p k s₀:ℝ) (hp:0<p) (hk:0<k) (hphys:2*p+2*k≤1),
    pstar≤p → pstar≤k → pstar≤s₀ → p≤1 → k≤1 → s₀≤1 →
    (Fintype.card U:ℝ)*(s₀/m)=D*k → (Fintype.card U:ℝ)*(s₀/m)*m=D*p →
    ∀ (q:U→Γ→ℝ) (hq:∀ u a,0≤q u a) (hQ:∀ u,∑ a,q u a≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a)) (a:Γ) (j:Color),
    (∀ u,q u a=s₀/m) → (∀ u,s u j=s₀) → pret*Fintype.card V≤(s₀/m)*Fintype.card U →
    1-χ-(Fintype.card V:ℝ)^(-Q)≤
      (rawMarkedRetentionLaw π d hd a p k hp.le hk.le hphys q hq hQ s hs hS).probability
      (fun z=>
        let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j;
        MarkedPackingLoadsWithSpokes P π d m D p k s₀ weight a j (Equiv.refl U) q s
          (τ+ε+11*((m:ℝ)+1)^4*(2*B/pstar^(2*m+1))*K*ζ) z.1 H) := by
  obtain ⟨M,N,hM,hN,hbase⟩:=marked_packing_adaptive_vortex_event m d hm hd B pstar ε K eta χ 0 Q pret ζ
    hB hpstar hε hK heta heta1 hχ hpret hζ
  refine ⟨M,N,hM,hN,?_⟩
  intro V U Γ Color _ _ _ _ _ _ _ hn hMV hMU hUV P π hnoshort D τ A hDlo hDhi weight hw p k s₀ hp hk hphys hpp hpk hps hp1 hk1 hs1 hmarked hord q hq hQ s hs hS a j ha hj hmass
  have hK: (Fintype.card U:ℝ)≤K*Fintype.card V:=by
    have hu:(Fintype.card U:ℝ)≤Fintype.card V:=by exact_mod_cast hUV
    nlinarith only [hu,mul_nonneg (sub_nonneg.mpr hK) (show (0:ℝ)≤Fintype.card V by positivity)]
  have hgraph:P.comap ((OrderIso.refl V).toOrderEmbedding)=P:=by ext x y; rfl
  have he:=hbase V U Γ Color (fun _=>V) (fun _=>U) (fun _=>U) hn hUV P π hnoshort
    (fun _=>(OrderIso.refl V).toOrderEmbedding) (fun _=>Function.Embedding.refl U) (fun _=>Function.Embedding.refl U)
    (fun _=>π) (by intros; rfl) 0 (by simp) (by intro i hi; exact hMV) (by intro i hi;exact hMU)
    (by intro i hi;omega) (by intro i hi;exact hK) (by intro i hi;exact hUV)
    (fun _=>D) τ A (by intro i hi;exact hDlo) (by intro i hi;exact hDhi)
    (fun _=>weight) (by intro i hi; simpa only [hgraph] using hw)
    p k s₀ hp hk hphys hpp hpk hps hp1 hk1 hs1 (by intro i hi;exact hmarked) (by intro i hi;exact hord)
    q hq hQ s hs hS a j ha hj hmass
  apply he.trans
  apply finiteLaw_probability_mono
  intro z hz
  have hh:=hz 0 (by omega) 0 (le_refl 0) (⊥:SimpleGraph V) (⊥:SimpleGraph (V⊕U))
    (by intro x; simp) (by intro x; simp)
  simp only [OrderIso.coe_toOrderEmbedding,OrderIso.coe_refl,Function.Embedding.coe_refl,id_eq,
    raw_marked_restrict_pair_identity,mul_zero,zero_div,add_zero,
    graph_bottom_edgeFinset_any_instance,rawMarkedDeleteRims_empty,markedDeletePhysicalSpokes_bottom] at hh
  have hgraphId:P.comap (id:V→V)=P:=by ext x y; rfl
  rw [hgraphId] at hh
  simpa only [Equiv.coe_refl] using hh
end Oberwolfach
