# Logic in Lean

By "logic" here we mean the study of propositions. A proposition is a
true/false statement. For example 2+2=4, 2+2=5, and the statement
of the Riemann Hypothesis are all propositions.

Basic mathematics with propositions involves learning about how
functions like `→`, `¬`, `∧`, `↔` and `∨` interact with
propositions like `true` and `false`.

In Lean we can prove mathematical theorems using *tactics* such as `intro`
and `apply`. The purpose of this section is to teach you ten or so basic
tactics which can be used to solve logic problems.

## Lean's notation for logic.

In Lean, `P : Prop` means "`P` is a proposition", and `P → Q` is the
proposition that "`P` implies `Q`". Note that Lean uses a single arrow `→`
rather than the double arrow `⇒`.

The notation `h : P` means any of the following equivalent things:

* `h` is a proof of `P`
* `h` is the assumption that `P` is true
* `P` is true, and this fact is called `h`

Here `h` is just a variable name. We will often call proofs of `P` things like `hP`
but you can call them pretty much anything.

WARNING: do not confuse `P : Prop` with `hP : P`. The former just means
that `P` is a true-false statement; the latter means that it is a true
statement.
