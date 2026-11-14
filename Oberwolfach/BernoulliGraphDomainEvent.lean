module

public import Oberwolfach.BernoulliFixedSetEvent
public import Oberwolfach.Neighbourhoods

@[expose] public section

/-! Size, degree and two-root counts for polynomially many bipartite
endpoint domains in one independent vertex sample. Every ambient root is
included, whether or not it survives the sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem bernoulli_graph_domain_common_event (ε:ℝ) (hε:0<ε) (q:ℕ):
    ∃ N:ℕ,∀ (V J:Type) [Fintype V] [DecidableEq V] [Fintype J],N≤Fintype.card V→
      Fintype.card J≤(Fintype.card V)^2→∀ (G:J→SimpleGraph V) (A B:J→Finset V)
      (p:ℝ) (hp:0≤p) (hp1:p≤1),
      1-1/(Fintype.card V:ℝ)^q≤
        (FiniteLaw.pi (fun _:V=>FiniteLaw.retentionCoin p hp hp1)).probability
          (fun σ=>∀ j,
            |(((A j)∩bernoulliVertexSet σ).card:ℝ)-p*(A j).card|<ε*Fintype.card V ∧
            |(((B j)∩bernoulliVertexSet σ).card:ℝ)-p*(B j).card|<ε*Fintype.card V ∧
            (∀ v,|((((A j)∩(G j).neighborFinset v)∩bernoulliVertexSet σ).card:ℝ)-
              p*((A j)∩(G j).neighborFinset v).card|<ε*Fintype.card V) ∧
            (∀ v,|((((B j)∩(G j).neighborFinset v)∩bernoulliVertexSet σ).card:ℝ)-
              p*((B j)∩(G j).neighborFinset v).card|<ε*Fintype.card V) ∧
            (∀ v w,|(((((B j)∩(G j).neighborFinset v)∩(G j).neighborFinset w)∩bernoulliVertexSet σ).card:ℝ)-
              p*(((B j)∩(G j).neighborFinset v)∩(G j).neighborFinset w).card|<ε*Fintype.card V)):=by
  obtain ⟨N,hN⟩:=bernoulli_fixed_sets_common_event 5 ε (by norm_num) hε 4 q
  refine ⟨max N 1,?_⟩
  intro V J _ _ _ hn hJ G A B p hp hp1
  let Test:=J×(Fin 2⊕V⊕V⊕(V×V))
  let sets:Test→Finset V:=fun t=>match t.2 with
    | Sum.inl i=>if i=0 then A t.1 else B t.1
    | Sum.inr (Sum.inl v)=>(A t.1)∩(G t.1).neighborFinset v
    | Sum.inr (Sum.inr (Sum.inl v))=>(B t.1)∩(G t.1).neighborFinset v
    | Sum.inr (Sum.inr (Sum.inr (v,w)))=>((B t.1)∩(G t.1).neighborFinset v)∩(G t.1).neighborFinset w
  have hn0:0<Fintype.card V:=by omega
  have hc:(Fintype.card Test:ℝ)≤5*(Fintype.card V:ℝ)^4:=by
    have hnR:(1:ℝ)≤Fintype.card V:=by exact_mod_cast hn0
    have hJ':(Fintype.card J:ℝ)≤(Fintype.card V:ℝ)^2:=by exact_mod_cast hJ
    have ht:(2:ℝ)+Fintype.card V+(Fintype.card V)+(Fintype.card V:ℝ)^2≤5*(Fintype.card V:ℝ)^2:=by
      nlinarith [sq_nonneg ((Fintype.card V:ℝ)-1)]
    have hprod:=mul_le_mul hJ' ht (by positivity) (by positivity)
    simp only [Test,Fintype.card_prod,Fintype.card_sum,Fintype.card_fin,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
    nlinarith only [hprod]
  have hh:=hN V Test (by omega) hc sets p hp hp1
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ j
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa only [sets,ite_true] using hσ (j,Sum.inl 0)
  · simpa only [sets,show ¬(1:Fin 2)=0 by decide,ite_false] using hσ (j,Sum.inl 1)
  · intro v;exact hσ (j,Sum.inr (Sum.inl v))
  · intro v;exact hσ (j,Sum.inr (Sum.inr (Sum.inl v)))
  · intro v w;exact hσ (j,Sum.inr (Sum.inr (Sum.inr (v,w))))

end Oberwolfach
