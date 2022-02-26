/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import linear_algebra.basis -- vector spaces and bases

/-!

# Steinitz exchange lemma

-/

-- This says "let `k` be a field and let `V` be a vector space over `k`"
variables (k : Type) [field k] (V : Type) [add_comm_group V] [module k V]

/-
Steinitz Exchange Lemma:

Let `V` be a vector space over the field `k`, and `X` be a subset of `V`.
Suppose `u ∈ Span(X)` but `u ∉ Span(X∖{v})` for some `v ∈ X`, and
let `Y = (X∖{v}) ∪ {u}`.
Then, `Span(X) = Span(Y)`
-/

variables {X Y : set V}
variables {u : V} {v : X}

-- let w be v (w : V)
-- let Z be X - {v}, so X = Z ∪ {v}
-- i.e. X = insert w Z
-- Y is insert u Z
variables (w : V) (Z : set V)

open submodule

lemma steinitz_exchange 
  (hu : u ∈ (submodule.span k (insert w Z)))
  (hnu : u ∉ submodule.span k Z) :
  submodule.span k (insert w Z) = submodule.span k (insert u Z) :=
begin
  apply le_antisymm,
    -- key lemma!
  { have hw := mem_span_insert_exchange hu hnu,
    rw span_le,
    rw set.insert_subset,
    refine ⟨hw, _⟩,
    rw ← span_le,
    apply span_mono,
    simp },
  -- Z ⊆ span (w ∪ Z)
  -- and by `hu`, u ∈ span (w ∪ Z)
  -- so span (u ∪ Z) ⊆ span (w ∪ Z)
  { 
    rw span_le,
    rw set.insert_subset,
    split,
    { exact hu,
    },
    { rw ← span_le,
      apply span_mono,
      simp }
  }
end

lemma steinitz_exchange'
    (hu : u ∈ (submodule.span k X))
    (hnu : u ∉ submodule.span k (X.diff {v})) 
    (hY : Y = (X.diff {v}).union {u}):
    submodule.span k X = submodule.span k Y :=
begin
  cases v with w hw,
  have hX : X = insert w (X \ {w}),
  { simp [hw] },
  convert steinitz_exchange k V w (X \ {w}) _ hnu,
  { change Y = (X \ {w}) ∪ {u} at hY,
    simpa using hY, 
  },
  { rwa ← hX }
end

lemma steinitz_exchange''
  (hu : u ∈ (submodule.span k X))
  (hnu : u ∉ submodule.span k (X \ {v})) 
    (hY : Y = (X \ {v}) ∪ {u}):
    submodule.span k X = submodule.span k Y :=
begin
  cases v with w hw,
  rw hY,
  simp,
  convert steinitz_exchange k V w (X \ {w}) _ hnu,
  { simp [hw] },
  convert hu,
  simp [hw],
end