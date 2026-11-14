module

public import Oberwolfach.MarkedBoundaryExtensionCoins
public import Oberwolfach.BernoulliPatternLowerEvent

@[expose] public section
/-! One fresh physical sample simultaneously retains many ordinary boundary
extension labels for every ordered pair of rim roots and every hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_boundary_extension_retention_event (β p:ℝ) (hβ:0<β) (hp:0<p) (hp1:p≤1) (q:ℕ):
    ∃N:ℕ,∀(V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
      N≤Fintype.card (V⊕U)→∀(Q:SimpleGraph V) (H:V→U→Prop) (X:Finset V),
      (∀a c u,β*Fintype.card (V⊕U)≤
        ((X.filter (fun v=>Q.Adj a v∧Q.Adj v c∧H v u)).card:ℝ))→
      1-1/(Fintype.card (V⊕U):ℝ)^q≤
        (FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1)).probability
          (fun σ=>∀a c u,p^3*β*Fintype.card (V⊕U)/2≤
            ((retainedPatternSet (X.filter (fun v=>Q.Adj a v∧Q.Adj v c∧H v u))
              (markedBoundaryJoinCoins a c u) σ).card:ℝ)):=by
  obtain ⟨N,hN⟩:=retained_pattern_lower_common_event 1 3 (p^3*β/2) (by norm_num) (by positivity) 3 3 q
  refine ⟨max 1 N,?_⟩
  intro V U _ _ _ _ hn Q H X hparent
  let n:=Fintype.card (V⊕U)
  let J:=V×V×U
  let A:J→Finset V:=fun t=>X.filter (fun v=>Q.Adj t.1 v∧Q.Adj v t.2.1∧H v t.2.2)
  let S:J→V→Finset (Sym2 (V⊕U)):=fun t=>markedBoundaryJoinCoins t.1 t.2.1 t.2.2
  have hV:Fintype.card V≤n:=by simp [n]
  have hU:Fintype.card U≤n:=by simp [n]
  have hVR:(Fintype.card V:ℝ)≤n:=Nat.cast_le.mpr hV
  have hUR:(Fintype.card U:ℝ)≤n:=Nat.cast_le.mpr hU
  have hJ:(Fintype.card J:ℝ)≤1*(n:ℝ)^3:=by
    simp only [J,Fintype.card_prod,Nat.cast_mul,one_mul]
    have hmul:(Fintype.card V:ℝ)*Fintype.card U≤(n:ℝ)^2:=by
      simpa only [pow_two] using mul_le_mul hVR hUR (Nat.cast_nonneg _) (by positivity:(0:ℝ)≤n)
    have hh:=mul_le_mul hVR hmul (by positivity:(0:ℝ)≤(Fintype.card V:ℝ)*Fintype.card U) (by positivity:(0:ℝ)≤n)
    nlinarith only [hh]
  have hsize (j:J) (v:V):(S j v).card≤3:=marked_boundary_join_coins_size j.1 j.2.1 j.2.2 v
  have haffect (j:J) (e:Sym2 (V⊕U)):((Finset.univ.filter (fun v=>e∈S j v)).card:ℝ)≤3:=by
    exact_mod_cast marked_boundary_join_coins_influence j.1 j.2.1 j.2.2 e
  have hh:=hN n (by dsimp [n];omega) V (Sym2 (V⊕U)) J hV hJ A S
    (fun j v _=>hsize j v) (fun j v=>by exact_mod_cast hsize j v) haffect p hp.le hp1
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ a c u
  have h:=hσ (a,c,u)
  have hc:=mul_le_mul_of_nonneg_left (hparent a c u) (pow_nonneg hp.le 3)
  dsimp [A,S,n] at h hc
  nlinarith only [h,hc]
end Oberwolfach
