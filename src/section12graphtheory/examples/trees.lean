/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import combinatorics.simple_graph.connectivity -- paths and walks etc

/-

# Trees

A graph is a tree if it's nonempty and for every pair of vertices
there's a unique path between them.

In this file I show that trees have no cycles.

-/

universe u₀

namespace simple_graph

/-- A graph is a tree if it's nonempty and for every pair of vertices
  there's a unique path between them. -/
def is_tree {V : Type u₀} (G : simple_graph V) : Prop :=
nonempty V ∧ ∀ u v : V, ∃! p : G.walk u v, p.is_path

/-- A graph is connected if it's nonempty and for every pair of vertices
  there's a path between them. -/
def is_connected {V : Type u₀} (G : simple_graph V) : Prop :=
nonempty V ∧ ∀ u v : V, ∃ p : G.walk u v, p.is_path

namespace is_tree

variables {V : Type u₀} {G : simple_graph V}

/-- Trees are connected. -/
lemma is_connected {V : Type u₀} {G : simple_graph V} 
  (h : G.is_tree) : G.is_connected :=
begin
  exact ⟨h.1, λ u v, exists_unique.exists (h.2 u v)⟩,
end

open simple_graph.walk

/-- A tree has no cycles. -/
lemma no_cycles [decidable_eq V] (hG : G.is_tree) (u : V) (p : G.walk u u) :
¬ p.is_cycle :=
begin
  intro hp,
  cases p with _ _ v _ huv q,
  { exact hp.ne_nil rfl, },
  { set w1 := cons huv nil with hw1,
    set w2 := q.reverse with hw2,
    have hw1path : w1.is_path,
    { simp,
      intro h,
      rw h at huv,
      exact G.loopless v huv },
    have hw2path : w2.is_path,
    { apply is_path.reverse,
      rw is_path_def,
      simpa using hp.support_nodup },
    have hw := exists_unique.unique (hG.2 u v) hw1path hw2path,
    rw [hw1, hw2] at hw,
    apply_fun reverse at hw,
    rw reverse_reverse at hw,
    rw ← hw at hp,
    simp at hp,
    replace hp := is_circuit.to_trail (is_cycle.to_circuit hp),
    rw is_trail_def at hp,
    simp at hp,
    apply hp,
    apply sym2.rel.swap },    
end

end is_tree

end simple_graph
