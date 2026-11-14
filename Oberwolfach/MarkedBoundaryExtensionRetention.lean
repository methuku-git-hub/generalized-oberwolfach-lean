module

public import Oberwolfach.MarkedBoundaryExtensionCoins
public import Oberwolfach.BernoulliPatternLowerEvent

@[expose] public section

/-! A fresh physical-edge event preserves every boundary extension with a
p^3 lower bound. The counting domains and parent arc types are fixed
before this exposure; the event includes all ambient roots simultaneously. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_boundary_extension_retention_event (β p:ℝ) (hβ:0<β) (hp:0<p) (hp1:p≤1) (q:ℕ):
    ∃ N:ℕ,∀ (V U E K:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
    N≤Fintype.card (V⊕U)→∀ (tail head:E→V) (ktail khead:K→V)
      (H₀ HK:V→U→Prop) (π:Equiv.Perm V) (X:Finset V),
    (∀ j x u,β*Fintype.card (V⊕U)≤((X.filter (fun z=>markedArcPresent tail head ktail khead j x z∧
      (if j then HK z u else H₀ z u))).card:ℝ))→
    (∀ j x y u,x≠(if j then π y else y)→β*Fintype.card (V⊕U)≤
      ((X.filter (fun z=>markedArcPresent tail head ktail khead false x z∧
        markedArcPresent tail head ktail khead j z y∧H₀ z u)).card:ℝ))→
    1-1/(Fintype.card (V⊕U):ℝ)^q≤
      (FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1)).probability
        (fun σ=>
          (∀ j x u,p^3*β*Fintype.card (V⊕U)/2≤
            ((retainedPatternSet (X.filter (fun z=>markedArcPresent tail head ktail khead j x z∧
              (if j then HK z u else H₀ z u))) (markedBoundaryStepCoins π j x u) σ).card:ℝ))∧
          (∀ j x y u,x≠(if j then π y else y)→p^3*β*Fintype.card (V⊕U)/2≤
            ((retainedPatternSet (X.filter (fun z=>markedArcPresent tail head ktail khead false x z∧
              markedArcPresent tail head ktail khead j z y∧H₀ z u))
              (markedBoundaryJoinCoins x (if j then π y else y) u) σ).card:ℝ))) :=by
  obtain ⟨N,hN⟩:=retained_pattern_lower_common_event 4 3 (p^3*β/2) (by norm_num) (by positivity) 3 3 q
  refine ⟨max 1 N,?_⟩
  intro V U E K _ _ _ _ hn tail head ktail khead H₀ HK π X hstep hjoin
  let n:=Fintype.card (V⊕U)
  let J:Type:=(Bool×V×U)⊕(Bool×V×V×U)
  let A:J→Finset V:=Sum.elim
    (fun t=>X.filter (fun z=>markedArcPresent tail head ktail khead t.1 t.2.1 z∧
      (if t.1 then HK z t.2.2 else H₀ z t.2.2)))
    (fun t=>X.filter (fun z=>markedArcPresent tail head ktail khead false t.2.1 z∧
      markedArcPresent tail head ktail khead t.1 z t.2.2.1∧H₀ z t.2.2.2))
  let S:J→V→Finset (Sym2 (V⊕U)):=Sum.elim
    (fun t=>markedBoundaryStepCoins π t.1 t.2.1 t.2.2)
    (fun t=>markedBoundaryJoinCoins t.2.1 (if t.1 then π t.2.2.1 else t.2.2.1) t.2.2.2)
  have hn0:0<n:=by dsimp [n];omega
  have hn1:(1:ℝ)≤n:=by exact_mod_cast hn0
  have hV:Fintype.card V≤n:=by simp [n]
  have hU:Fintype.card U≤n:=by simp [n]
  have hVR:(Fintype.card V:ℝ)≤n:=Nat.cast_le.mpr hV
  have hUR:(Fintype.card U:ℝ)≤n:=Nat.cast_le.mpr hU
  have hJ:(Fintype.card J:ℝ)≤4*(n:ℝ)^3:=by
    simp only [J,Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    have hmul: (Fintype.card V:ℝ)*Fintype.card U≤(n:ℝ)^2:=by
      simpa only [pow_two] using mul_le_mul hVR hUR (Nat.cast_nonneg _) (by positivity : (0:ℝ)≤n)
    have hmul2:(Fintype.card V:ℝ)*((Fintype.card V:ℝ)*Fintype.card U)≤(n:ℝ)^3:=by
      have hh:=mul_le_mul hVR hmul (by positivity : (0:ℝ)≤(Fintype.card V:ℝ)*Fintype.card U) (by positivity : (0:ℝ)≤n)
      nlinarith only [hh]
    have hs:(n:ℝ)^2≤(n:ℝ)^3:=by nlinarith [sq_nonneg (n:ℝ)]
    nlinarith only [hmul,hmul2,hs]
  have hsize (j:J) (z:V):(S j z).card≤3:=by
    cases j with
    | inl t=>exact marked_boundary_step_coins_size π t.1 t.2.1 t.2.2 z
    | inr t=>exact marked_boundary_join_coins_size t.2.1 (if t.1 then π t.2.2.1 else t.2.2.1) t.2.2.2 z
  have haffect (j:J) (e:Sym2 (V⊕U)):
      ((Finset.univ.filter (fun z=>e∈S j z)).card:ℝ)≤3:=by
    cases j with
    | inl t=>exact_mod_cast marked_boundary_step_coins_influence π t.1 t.2.1 t.2.2 e
    | inr t=>exact_mod_cast marked_boundary_join_coins_influence t.2.1 (if t.1 then π t.2.2.1 else t.2.2.1) t.2.2.2 e
  have hh:=hN n (by dsimp [n];omega) V (Sym2 (V⊕U)) J hV hJ A S
    (fun j z _=>hsize j z) (fun j z=>by exact_mod_cast hsize j z) haffect p hp.le hp1
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ
  constructor
  · intro j x u
    have h:=hσ (Sum.inl (j,x,u))
    have hc:=mul_le_mul_of_nonneg_left (hstep j x u) (pow_nonneg hp.le 3)
    dsimp [A,S] at h
    dsimp [n] at h hc
    nlinarith only [h,hc]
  · intro j x y u hxy
    have h:=hσ (Sum.inr (j,x,y,u))
    have hc:=mul_le_mul_of_nonneg_left (hjoin j x y u hxy) (pow_nonneg hp.le 3)
    dsimp [A,S] at h
    dsimp [n] at h hc
    nlinarith only [h,hc]
end Oberwolfach
