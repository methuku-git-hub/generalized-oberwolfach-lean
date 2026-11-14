module

public import Oberwolfach.ParitySwitchRepair
public import Oberwolfach.ColouredTwoPaths

@[expose] public section

/-! Pair the actual odd complement degrees and realise every pair in the
single fixed coloured graph. No candidate set is resampled after pairing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem parity_repair_from_coloured_paths {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {q : ℕ} (hq : Even q) (G : SimpleGraph V) (σ : Sym2 V → Fin (q+1))
    (ρ : ℝ) (L : ℕ) (hL : 0<L)
    (hpath : ∀ a : Fin q,∀ u v,u≠v → ρ*Fintype.card V≤
      (colouredTwoPathCount G σ u v a.castSucc (Fin.last q):ℝ))
    (hlarge : (q:ℝ)*Fintype.card V/L+4*q+4*L<ρ*Fintype.card V) :
    ∃ τ : Sym2 V → Fin (q+1),
      (∀ a,(edgeColourGraph G τ a).edgeFinset.card=(edgeColourGraph G σ a).edgeFinset.card) ∧
      (∀ a v,Even ((G\edgeColourGraph G τ a).degree v)) ∧
      (∀ a v,|((edgeColourGraph G τ a).degree v:ℝ)-((edgeColourGraph G σ a).degree v:ℝ)|≤q+1) := by
  let T (j : Fin q) := Finset.univ.filter (fun v => Odd ((G\edgeColourGraph G σ j.castSucc).degree v))
  have hTeven (j : Fin q) : Even (T j).card := odd_complement_degree_set_even G (edgeColourGraph G σ j.castSucc)
  choose m hm he using fun j : Fin q => even_finset_pairing (T j) (hTeven j)
  let e (j : Fin q) : (Fin (m j)×Bool)≃T j := Classical.choice (he j)
  let I := (j : Fin q)×Fin (m j)
  let x (i : I) := (e i.1 (i.2,false)).val
  let y (i : I) := (e i.1 (i.2,true)).val
  have hxy (i : I) : x i≠y i := pairing_endpoints_distinct (e i.1) i.2
  let C (i : I) := (G.neighborFinset (x i)∩G.neighborFinset (y i)).filter
    (fun w => σ s(x i,w)=i.1.castSucc ∧ σ s(w,y i)=Fin.last q)
  have hI : Fintype.card I≤q*Fintype.card V := by
    have hmle (j : Fin q) : m j≤Fintype.card V := by
      have hh := Finset.card_le_univ (T j)
      rw [hm j] at hh
      omega
    simp only [I,Fintype.card_sigma,Fintype.card_fin]
    calc
      _ ≤ ∑ _ : Fin q,Fintype.card V := Finset.sum_le_sum (fun j _ => hmle j)
      _ = _ := by simp
  have hx (v : V) : ((Finset.univ.filter (fun i : I => x i=v)).card:ℝ)≤q := by
    dsimp only [I,x]
    have hh := paired_family_endpoint_bound T m e v false
    simp only [Fintype.card_fin] at hh
    exact_mod_cast hh
  have hy (v : V) : ((Finset.univ.filter (fun i : I => y i=v)).card:ℝ)≤q := by
    dsimp only [I,y]
    have hh := paired_family_endpoint_bound T m e v true
    simp only [Fintype.card_fin] at hh
    exact_mod_cast hh
  have hC (i : I) : (Fintype.card I:ℝ)/L+4*(q:ℝ)+4*L<(C i).card := by
    have hi : (Fintype.card I:ℝ)≤(q:ℝ)*Fintype.card V := by exact_mod_cast hI
    have hd := div_le_div_of_nonneg_right hi (Nat.cast_nonneg (α:=ℝ) L)
    have hp := hpath i.1 (x i) (y i) (hxy i)
    change ρ*Fintype.card V≤((C i).card:ℝ) at hp
    linarith only [hd,hlarge,hp]
  obtain ⟨z,hz,hd,_⟩ := undirectedTwoPathPacking_exists x y C L hL hx hy hC
  have hzx (i : I) : G.Adj (x i) (z i) :=
    (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp (Finset.mem_filter.mp (hz i)).1).1
  have hzy (i : I) : G.Adj (z i) (y i) :=
    ((G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp (Finset.mem_filter.mp (hz i)).1).2).symm
  have hc0 (i : I) : σ s(x i,z i)=i.1.castSucc := (Finset.mem_filter.mp (hz i)).2.1
  have hc1 (i : I) : σ s(z i,y i)=Fin.last q := (Finset.mem_filter.mp (hz i)).2.2
  obtain ⟨τ,hcard,hparity,hdeg,hlast⟩ := paired_colour_parity_repair hq G σ T m e
    (fun j v => by simp only [T,Finset.mem_filter,Finset.mem_univ,true_and]) z hd hzx hzy hc0 hc1
  refine ⟨τ,hcard,hparity,?_⟩
  intro a v
  refine Fin.lastCases ?_ (fun j => ?_) a
  · exact (hlast v).trans (by linarith)
  · exact (hdeg j v).trans (by have hq0 : (0:ℝ)≤q := Nat.cast_nonneg _;linarith)

end Oberwolfach
