import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Tactic.Linarith
open BigOperators

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V}

/-- A *Hamiltonian path* is a walk `p` that visits every vertex exactly once. -/
def SimpleGraph.Walk.IsHamiltonian (p : G.Walk u v) : Prop :=
  ∀ v : V, p.support.count v = 1

/-- If `p` is a Hamiltonian path and `w` is a member of the vertex set of `p`, `w` is visited by `p`.-/
lemma SimpleGraph.Walk.IsHamiltonian.contains_vertex (p : G.Walk u v) (hp : p.IsHamiltonian)
    (w : V) : w ∈ p.support := by
  specialize hp w
  rw [←List.count_pos_iff_mem, hp]
  norm_num1

/-- If `p` is a Hamiltonian path of a graph `G` its length is one less than the number of vertices of `G`.-/
lemma SimpleGraph.Walk.IsHamiltonian.length (p : G.Walk u v) (hp : p.IsHamiltonian) :
    p.length = Fintype.card V - 1 := by
    dsimp only [IsHamiltonian] at hp
    have length_relation : p.length = p.support.length - 1
    · cases p
      case nil =>
        rfl
      case cons h' p' =>
      simp
    · have : p.support.length = Fintype.card V
      · have : ∑ u : V, p.support.count u = Fintype.card V - 1
        · sorry
        . sorry
      · rw [this] at length_relation
        sorry
        -- exact Iff.mp Nat.succ_inj' length_relation

lemma Nil_iff_eq_nil {v : V} : ∀ p : G.Walk v v, p.Nil ↔ p = SimpleGraph.Walk.nil
| .nil | .cons _ _ => by simp

/-- A *Hamiltonian cycle* is a cycle `p` that visits every vertex once.-/
structure SimpleGraph.Walk.IsHamiltonianCycle (p : G.Walk v v) extends p.IsCycle : Prop :=
(path_hamiltonian : (p.tail (by
  intro np
  rw [Nil_iff_eq_nil p] at np
  contradiction
)).IsHamiltonian)

lemma SimpleGraph.Walk.support_of_tail_eq_tail_of_support (p : G.Walk v v) (hnil : ¬p.Nil) : (p.tail hnil).support = p.support.tail := by
  rw [←SimpleGraph.Walk.cons_support_tail p hnil]
  rw [@List.tail_cons]

lemma SimpleGraph.Walk.IsHamiltonianCycle.contains_vertex (p : G.Walk v v) (hp : p.IsHamiltonianCycle)
    (w : V) : w ∈ p.support := by
    have : w ∈ p.support.tail
    · have hnil : ¬ Nil p
      · rw [Nil_iff_eq_nil]
        apply hp.ne_nil
      · rw [←SimpleGraph.Walk.support_of_tail_eq_tail_of_support p hnil]
        apply SimpleGraph.Walk.IsHamiltonian.contains_vertex (p.tail hnil) hp.path_hamiltonian w
    · exact List.mem_of_mem_tail this

lemma SimpleGraph.Walk.IsHamiltonianCycle.length (p : G.Walk v v) (hp : p.IsHamiltonianCycle) :
  p.length = Fintype.card V := by
  have hnil : ¬p.Nil := by rw [Nil_iff_eq_nil]; apply hp.ne_nil
  rw [←SimpleGraph.Walk.length_tail_add_one hnil]
  have : (p.tail hnil).length = Fintype.card V - 1
  · apply SimpleGraph.Walk.IsHamiltonian.length
    exact hp.path_hamiltonian
  · rw [this]
    rw [tsub_add_eq_add_tsub]
    · simp
    · rw [@Nat.succ_le]
      rw [Fintype.card_pos_iff]
      exact Nonempty.intro v

-- BM: `cons_isCycle_iff` will be useful for going between hamiltonian cycles and paths
lemma SimpleGraph.Walk.IsHamiltonianCycle.cycle (p : G.Walk v v) (hp : p.IsHamiltonianCycle) :
    p.IsCycle := by
  exact hp.toIsCycle

/-- A *Hamiltonian graph* `G` is a *connected graph* that contains a *Hamiltonian cycle* `p`.
    By convention, the singleton graph is considered to be Hamiltonian. -/
def SimpleGraph.IsHamiltonian (G : SimpleGraph V) : Prop :=
  (G.Connected ∧ ∃ v, ∃ p : G.Walk v v, p.IsHamiltonianCycle) ∨ (Fintype.card V = 1)

-- /-- Dirac's theorem (1952): Let |G| = n ≥ 3 ∧ δ(G) ≥ n/2 → G is *hamiltonian*. -/
-- theorem Dirac {G : SimpleGraph V} [DecidableRel G.Adj] (CardinalityCondition: Fintype.card V ≥ 3) (MinDegreeCondition: G.minDegree ≥ Fintype.card V/2) : G.IsHamiltonian := by
--  sorry
