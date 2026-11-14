module

public import Oberwolfach.MarkedBoundaryExtensionCoins
public import Oberwolfach.BernoulliPatternLowerEvent

@[expose] public section
/-! Fresh physical sampling retains simultaneous two-spoke hub choices for
all rim pairs; no independence between pairs is required. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 11000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinaryBoundaryHubPairCoins (a c:V) (u:U):Finset (Sym2 (V⊕U)):=
  {s(Sum.inl a,Sum.inr u),s(Sum.inl c,Sum.inr u)}

theorem ordinary_boundary_hub_pair_coin_influence (a c:V) (e:Sym2 (V⊕U)):
    (Finset.univ.filter (fun u=>e∈ordinaryBoundaryHubPairCoins a c u)).card≤2:=by
  have h1 (v:V):Function.Injective (fun u:U=>(s(Sum.inl v,Sum.inr u):Sym2 (V⊕U))):=by
    intro u w h
    rcases Sym2.eq_iff.mp h with ⟨_,h⟩|⟨h,_⟩
    · exact Sum.inr.inj h
    · exact (Sum.inl_ne_inr h).elim
  have hcard (v:V):(Finset.univ.filter (fun u=>e=s(Sum.inl v,Sum.inr u))).card≤1:=by
    apply Finset.card_le_one.mpr
    intro u hu w hw
    exact h1 v ((Finset.mem_filter.mp hu).2.symm.trans (Finset.mem_filter.mp hw).2)
  have he:Finset.univ.filter (fun u=>e∈ordinaryBoundaryHubPairCoins a c u)=
      (Finset.univ.filter (fun u=>e=s(Sum.inl a,Sum.inr u)))∪
        (Finset.univ.filter (fun u=>e=s(Sum.inl c,Sum.inr u))):=by
    ext u;simp [ordinaryBoundaryHubPairCoins]
  rw [he]
  have hh:=Finset.card_union_le (Finset.univ.filter (fun u=>e=s(Sum.inl a,Sum.inr u)))
    (Finset.univ.filter (fun u=>e=s(Sum.inl c,Sum.inr u)))
  have ha:=hcard a
  have hc:=hcard c
  omega

theorem ordinary_boundary_hub_pair_retention_event (β p:ℝ) (hβ:0<β) (hp:0<p) (hp1:p≤1) (q:ℕ):
    ∃N:ℕ,∀(V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
      N≤Fintype.card (V⊕U)→∀(H:V→U→Prop) (Z:Finset U),
      1-1/(Fintype.card (V⊕U):ℝ)^q≤
        (FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1)).probability
          (fun σ=>∀a c,β*Fintype.card (V⊕U)≤((Z.filter (fun u=>H a u∧H c u)).card:ℝ)→
            p^2*β*Fintype.card (V⊕U)/2≤
              ((retainedPatternSet (Z.filter (fun u=>H a u∧H c u)) (ordinaryBoundaryHubPairCoins a c) σ).card:ℝ)):=by
  obtain ⟨N,hN⟩:=retained_pattern_lower_common_event 1 2 (p^2*β/2) (by norm_num) (by positivity) 2 2 q
  refine ⟨max 1 N,?_⟩
  intro V U _ _ _ _ hn H Z
  let n:=Fintype.card (V⊕U)
  let J:=V×V
  let A:J→Finset U:=fun t=>Z.filter (fun u=>H t.1 u∧H t.2 u)
  let S:J→U→Finset (Sym2 (V⊕U)):=fun t=>ordinaryBoundaryHubPairCoins t.1 t.2
  have hV:Fintype.card V≤n:=by simp [n]
  have hU:Fintype.card U≤n:=by simp [n]
  have hVR:(Fintype.card V:ℝ)≤n:=Nat.cast_le.mpr hV
  have hJ:(Fintype.card J:ℝ)≤1*(n:ℝ)^2:=by
    simp only [J,Fintype.card_prod,Nat.cast_mul,one_mul,pow_two]
    exact mul_self_le_mul_self (Nat.cast_nonneg _) hVR
  have hsize (j:J) (u:U):(S j u).card≤2:=by
    unfold S ordinaryBoundaryHubPairCoins
    have hh:=Finset.card_insert_le (s(Sum.inl j.1,Sum.inr u):Sym2 (V⊕U)) {s(Sum.inl j.2,Sum.inr u)}
    simp only [Finset.card_singleton] at hh
    omega
  have haffect (j:J) (e:Sym2 (V⊕U)):((Finset.univ.filter (fun u=>e∈S j u)).card:ℝ)≤2:=by
    exact_mod_cast ordinary_boundary_hub_pair_coin_influence j.1 j.2 e
  have hh:=hN n (by dsimp [n];omega) U (Sym2 (V⊕U)) J hU hJ A S
    (fun j u _=>hsize j u) (fun j u=>by exact_mod_cast hsize j u) haffect p hp.le hp1
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ a c hparent
  have h:=hσ (a,c)
  have hc:=mul_le_mul_of_nonneg_left hparent (pow_nonneg hp.le 2)
  dsimp [A,S,n] at h hc
  nlinarith only [h,hc]
end Oberwolfach
