module

public import Oberwolfach.MarkedBoundaryExtensionCoins
public import Oberwolfach.BernoulliPatternLowerEvent

@[expose] public section

/-! Retention of compatible inner hubs for every pair of row roots.
Both spoke tests use the original physical coins, with all parent
candidate sets fixed before exposure. The event also covers root pairs
whose parent count is too small to be used later. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def markedBoundaryHubCoins (x y:V) (u:U):Finset (Sym2 (V⊕U)):=
  {s(Sum.inl x,Sum.inr u),s(Sum.inl y,Sum.inr u)}

theorem marked_boundary_hub_coins_size (x y:V) (u:U):
    (markedBoundaryHubCoins x y u).card≤3:=by
  have h:=Finset.card_insert_le (s(Sum.inl x,Sum.inr u):Sym2 (V⊕U)) {s(Sum.inl y,Sum.inr u)}
  simp only [Finset.card_singleton] at h
  exact h.trans (by omega)

theorem marked_boundary_hub_coins_influence (x y:V) (e:Sym2 (V⊕U)):
    (Finset.univ.filter (fun u=>e∈markedBoundaryHubCoins x y u)).card≤3:=by
  have hx:Function.Injective (fun u:U=>(s(Sum.inl x,Sum.inr u):Sym2 (V⊕U))):=by
    intro u v h;exact Sum.inr.inj (Sym2.congr_right.mp h)
  have hy:Function.Injective (fun u:U=>(s(Sum.inl y,Sum.inr u):Sym2 (V⊕U))):=by
    intro u v h;exact Sum.inr.inj (Sym2.congr_right.mp h)
  have h:=three_injective_coin_maps_influence
    (fun u:U=>(s(Sum.inl x,Sum.inr u):Sym2 (V⊕U)))
    (fun u:U=>(s(Sum.inl y,Sum.inr u):Sym2 (V⊕U)))
    (fun u:U=>(s(Sum.inl y,Sum.inr u):Sym2 (V⊕U))) hx hy hy e
  simpa only [markedBoundaryHubCoins,Finset.insert_eq_of_mem (Finset.mem_singleton_self _)] using h

theorem marked_boundary_hub_retention_event (ε:ℝ) (hε:0<ε) (q:ℕ):
    ∃ N:ℕ,∀ (V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
    N≤Fintype.card (V⊕U)→∀ (H₀ HK:V→U→Prop) (Z:Finset U),
    ∀ (p:ℝ) (hp:0≤p) (hp1:p≤1),
    1-1/(Fintype.card (V⊕U):ℝ)^q≤
      (FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp hp1)).probability
        (fun σ=>∀ (j:Bool) x y,
          p^3*(Z.filter (fun u=>H₀ x u∧(if j then HK y u else H₀ y u))).card-ε*Fintype.card (V⊕U)<
          ((retainedPatternSet (Z.filter (fun u=>H₀ x u∧(if j then HK y u else H₀ y u)))
            (markedBoundaryHubCoins x y) σ).card:ℝ)):=by
  obtain ⟨N,hN⟩:=retained_pattern_lower_common_event 2 3 ε (by norm_num) hε 3 2 q
  refine ⟨N,?_⟩
  intro V U _ _ _ _ hn H₀ HK Z p hp hp1
  let n:=Fintype.card (V⊕U)
  have hV:(Fintype.card V:ℝ)≤n:=by exact_mod_cast (show Fintype.card V≤n by simp [n])
  have hJ:(Fintype.card (Bool×V×V):ℝ)≤2*(n:ℝ)^2:=by
    simp only [Fintype.card_prod,Fintype.card_bool,Nat.cast_mul,Nat.cast_ofNat]
    have hh:=mul_le_mul hV hV (Nat.cast_nonneg _) (Nat.cast_nonneg n)
    nlinarith only [hh]
  have hh:=hN n hn U (Sym2 (V⊕U)) (Bool×V×V) (by simp [n]) hJ
    (fun j=>Z.filter (fun u=>H₀ j.2.1 u∧(if j.1 then HK j.2.2 u else H₀ j.2.2 u)))
    (fun j=>markedBoundaryHubCoins j.2.1 j.2.2)
    (fun j u _=>marked_boundary_hub_coins_size j.2.1 j.2.2 u)
    (fun j u=>by exact_mod_cast marked_boundary_hub_coins_size j.2.1 j.2.2 u)
    (fun j e=>by exact_mod_cast marked_boundary_hub_coins_influence j.2.1 j.2.2 e) p hp hp1
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ j x y
  exact hσ (j,x,y)
end Oberwolfach
