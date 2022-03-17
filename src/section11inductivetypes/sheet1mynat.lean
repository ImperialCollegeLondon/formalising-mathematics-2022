/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Behind the scenes at the natural number game

I explain a bit about how inductive types and inductive definitions work.

## How to make the natural numbers?

I present the natural numbers in the natural number game
(TODO add URL) as "something with zero and succ which
satisfies induction" and I present addition as "something
which by definition satisfies `x+0=x` and `x+succ(y)=succ(x+y)`.
Here's how it actually happens.

-/

inductive mynat : Type -- note no `:=` next; this is a different kind of definition
| zero : mynat
| succ (n : mynat) : mynat

/-

This "inductive definition" creates four things automatically:
(1) a new type called `mynat : Type`
(2) a new term `mynat.zero : mynat`
(3) a new function `mynat.succ : mynat → mynat`
(4) a "recursor" -- something I'll tell you about in a minute.

Right now, the `0` in `mynat` is called `mynat.zero`. However if
we `open mynat` or move into the `mynat` namespace with `namespace mynat`, 
it will just be called `zero`. 
-/

-- #check zero -- doesn't work

namespace mynat

-- now zero works:

-- #check zero -- zero : mynat

-- but `0` still doesn't work:

-- #check (0 : mynat) -- failed to find `⊢ has_zero mynat`

/-

To get `0` working, let's make an instance of `has_zero mynat`.

-/

instance : has_zero mynat :=
{ zero := zero }

-- #check (0 : mynat) -- works

-- We could even make a `simp` lemma which turns `mynat.zero` into `0`.

@[simp] lemma mynat.zero_eq_zero : mynat.zero = 0 :=
begin
  refl
end

-- Now if we ever see a `mynat.zero` we can `simp` it into `0`.

/-

## The recursor

The fourth thing which magically appears after our definition of `mynat`
is a new (quite complicated) function `mynat.rec`, which is at once
the principles of induction and recursion.

The reason `mynat.rec` can be both is that it mentions a term
`motive : mynat → Sort u` and `Sort u` is Lean's way of saying
"any universe -- either `Prop` or `Type` (or even the higher universes)".
Let's see what `mynat.rec` looks like in the special cases of `Prop`
and `Type`:

-/

-- induction: how to prove P(n) for all n, where P(n) is a proposition
-- using mynat.rec directly
example 
  -- let P be a family of true-false statements
  (P : mynat → Prop) 
  -- Assume P(0) is true
  (h0 : P mynat.zero)
  -- assume P(n) implies P(succ n)
  (hsucc : ∀ n : mynat, P n → P (mynat.succ n))
  -- Then
  :
  -- P(n) is true for all n
  ∀ n, P n :=
begin
  -- apply mynat.rec
  exact mynat.rec h0 hsucc
end

-- recursion: how to define f(n) for all n, given f(0) and
-- a formula for f(n+1) which can depend on f(n) (and on n)

example
  -- let X be a type
  (X : Type)
  -- Say we have x₀ in X (the value of f(0))
  (x₀ : X)
  -- and say we have a function mynat → X → X, for example
  -- if X is the reals and f(n+1)= 1/n + f(n) then this function would 
  -- be λ n x, 1/n + x
  (I : mynat → X → X)
  -- then 
  :
  -- we can build a function mynat → X
  mynat → X :=
@mynat.rec (λ _, X) x₀ I

/-

This is not now we use the recursor though.
In term mode, we use recursive definitions; in tactic
mode we use the induction tactic.

Let's see these in action, with our first inductive definition,
namely addition.

-/

def add : mynat → mynat → mynat -- again no `:=`
| n 0 := n -- n + 0 defined to be n
| n (succ m) := succ (add n m)

/-

Again we see these weird `|` symbols, but this time what's happening
is not that we are defining a new inductive type, but we are defining
a new function which eats inductive types and is defined on a case
by case basis; it's "defined by recursion". Internally the definition
of `add` uses `mynat.rec` but we don't have to worry about that any more.
This way of working with the recursor is far less painful.

Now `add_zero` and `add_succ` are definitional. Let's see this.
First let's set up notation `+` for addition with the notational
typeclass `has_add`

-/

instance : has_add mynat :=
{ add := add }

lemma add_zero (n : mynat) : n + 0 = n :=
begin
  refl
end

-- dot notation for succ is quite confusing; let's switch it off
attribute [pp_nodot] mynat.succ

lemma add_succ (n m : mynat) : n + succ m = succ (n + m) :=
begin
  refl
end

/-
If you've played the natural number game, you might now be
able to find shorter proofs of things. For example `n + 0 = n`
can be proved by `refl` even though I never explain this.

The `induction` tactic automatically works for `mynat` now
because it knows about `mynat.rec`.
-/

lemma zero_add (n : mynat) : 0 + n = n :=
begin
  induction n with d hd, -- works!
  { 
    -- see how we have a mixture of notation now? :-(
    -- see if you can sort out the mess. In the natural number game
    -- I do this behind the scenes.
    sorry }, -- 
  { sorry }
end

/-

Later on in the natural number game I randomly introduce two new
theorems: `zero_ne_succ` (saying `0 ≠ succ n`) and `succ_inj` (saying
that `succ m = succ n → m = n`). Here's how we prove them. Let's
make a new inductive type with two terms.

-/

/-- The type `yesno` has two terms, `yesno.yes` and `yesno.no`. -/
inductive yesno : Type
| yes : yesno
| no : yesno

open yesno

-- now they're just called `yes` and `no`.

example : yes ≠ no :=
begin
  intro h, -- h : yes = no
  cases h, -- no cases where this is true. Proved using yesno.rec ;-)
end

example : yes ≠ no. -- a complete proof! Proof is "there are no cases"

-- now let's define a function `is_zero`

@[pp_nodot]
def is_zero : mynat → yesno
| 0 := yes
| (succ n) := no

lemma yes_zero_is_zero : is_zero 0 = yes :=
begin
  refl
end

lemma no_succ_isnt_zero (n : mynat) : is_zero (succ n) = no :=
begin
  refl
end

lemma succ_ne_zero (n : mynat) : succ n ≠ 0 :=
begin
  -- see if you can prove it.
  -- Recall the `apply_fun` tactic which can turn a hypothesis
  -- `x = y` into `f x = f y`
  sorry
end

-- Now here's how to prove that `succ` is injective

@[pp_nodot]
def pred : mynat → mynat
| 0 := succ (succ (succ (succ (succ (succ (succ 0)))))) -- junk value
| (succ n) := n -- what we care about

lemma pred_succ (n : mynat) : pred (succ n) = n :=
begin
  sorry
end

lemma succ_inj (a b : mynat) (hab : succ a = succ b) : a = b :=
begin
  sorry,
end

end mynat
