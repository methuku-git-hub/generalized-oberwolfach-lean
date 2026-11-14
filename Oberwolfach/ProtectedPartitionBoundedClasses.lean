module

public import Oberwolfach.ProtectedPartitionFamily

@[expose] public section
/-! The class count is chosen after the host and prescribed factors, but is
bounded by the fixed cutoff. A single order threshold therefore suffices for
all possible positive class counts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem protected_partition_bounded_classes (K:ℕ) {α r ξ:ℝ}
    (hα:0<α) (hr:0<r) (hξ:0<ξ) (B:ℕ):
    ∃ N₀:ℕ,∀ k:ℕ,0<k→k≤K+1→∀ n≥N₀,∀ (G:SimpleGraph (Fin n)) (D:ℕ)
      (m:Fin k→ℕ) (ρ:Fin k→ℝ)
      (hρ:∀ a,0≤ρ a) (htotal:∑ a,ρ a=1),
      G.IsRegularOfDegree D→Even D→(1/2+α)*n≤(D:ℝ)→
      (∑ a,m a=D/2)→(∀ a,ρ a/2*D=(m a:ℝ))→
      (∀ a,r≤ρ a)→∀ I:Fin k→Finset (Fin n),
      ((∑ a,(I a).card:ℕ):ℝ)≤α/100000*n→
      1-1/(n:ℝ)^10≤
        (FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.categorical ρ hρ htotal)).probability
          (fun c=>∀ A:Fin k→SimpleGraph (Fin n),
            (∀ a,A a≤edgeColourGraph G c a)→
            (∑ a,(A a).edgeFinset.card)≤B→
            ∃ H:Fin k→SimpleGraph (Fin n),
              EdgePartition G H ∧ (∀ a,(H a).IsRegularOfDegree (2*m a)) ∧
              (∀ a,A a≤H a) ∧
              (∀ a b x,x∈I b→∀ y,y∈I b→
                ((H a).Adj x y↔(edgeColourGraph G c a).Adj x y)) ∧
              (∀ a x,((Finset.univ.filter (fun y=>
                Xor ((H a).Adj x y) ((edgeColourGraph G c a).Adj x y))).card:ℝ)≤ξ*n)):=by
  have hN (i:Fin (K+1)):=protectedRegularPartition_family_highProbability
    (show 0 < i.val+1 by omega) hα (fun _=>r) (fun _=>ξ) (fun _=>hr) (fun _=>hξ) B
  let Ns:Fin (K+1)→ℕ:=fun i=>Classical.choose (hN i)
  let N₀:=∑ i,Ns i
  refine ⟨N₀,?_⟩
  intro k hk hkK n hn
  let i:Fin (K+1):=⟨k-1,by omega⟩
  have hi:i.val+1=k:=by dsimp [i];omega
  have hNs:Ns i≤N₀:=Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
  have hspec:=Classical.choose_spec (hN i)
  have hspec':∀ n≥Ns i,∀ (G:SimpleGraph (Fin n)) (D:ℕ)
      (m:Fin (i.val+1)→ℕ) (ρ:Fin (i.val+1)→ℝ)
      (hρ:∀ a,0≤ρ a) (htotal:∑ a,ρ a=1),
      G.IsRegularOfDegree D→Even D→(1/2+α)*n≤(D:ℝ)→
      (∑ a,m a=D/2)→(∀ a,ρ a/2*D=(m a:ℝ))→
      (∀ a,r≤ρ a)→∀ I:Fin (i.val+1)→Finset (Fin n),
      ((∑ a,(I a).card:ℕ):ℝ)≤α/100000*n→
      1-1/(n:ℝ)^10≤
        (FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.categorical ρ hρ htotal)).probability
          (fun c=>∀ A:Fin (i.val+1)→SimpleGraph (Fin n),
            (∀ a,A a≤edgeColourGraph G c a)→
            (∑ a,(A a).edgeFinset.card)≤B→
            ∃ H:Fin (i.val+1)→SimpleGraph (Fin n),
              EdgePartition G H ∧ (∀ a,(H a).IsRegularOfDegree (2*m a)) ∧
              (∀ a,A a≤H a) ∧
              (∀ a b x,x∈I b→∀ y,y∈I b→
                ((H a).Adj x y↔(edgeColourGraph G c a).Adj x y)) ∧
              (∀ a x,((Finset.univ.filter (fun y=>
                Xor ((H a).Adj x y) ((edgeColourGraph G c a).Adj x y))).card:ℝ)≤ξ*n)):=by
    exact hspec
  rw [hi] at hspec'
  exact hspec' n (hNs.trans hn)
end Oberwolfach
