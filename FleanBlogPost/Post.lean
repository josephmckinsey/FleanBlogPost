/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import FleanBlogPost.Page

#doc (Page) "Flean: Floating point numbers in lean, mostly" =>
> Note: this probably won't make sense to anyone who hasn't tried to learn Lean yet. Do it! There's a [game version with natural numbers](https://adam.math.hhu.de/), which is quite approachable.

TLDR: Implementing floating point numbers in Lean taught me a lot about floating point numbers. It sharpened my thinking, helped me learn more mathematics in Lean, and it helped me understand founding as a concept.

See my previous post on [Flean](https://josephmckinsey.com/flean.html) for background on why I decided to do this.

# Approaches for Floating Point Number Proofs

Typically, there are two ways you can prove things about floating point number computations in a theorem-proving language. Either you use interval arithmetic to bound calculations, or you bound the error more loosely with each operation.

Interval arithmetic is better at tight bounds and chaining computations, since it packages error propagation generally with the rounding to floats. There are also more extensions for correlating error across computations. You also don't need to prove anything about conditions of your floating point number, since you get a bound for your specific input. That's really convenient for arbitrary computations.

More traditional numerical analysis models each operation as introducing some absolute or relative error, which can be propagated into other errors as numbers are added or multiplied. This becomes quite annoying when you have to mix absolute and relative error, which is often, and long running computations can produce extremely loose and large error bounds.

Creating functions with small errors is also extremely tricky. Many common functions such as $`\sin` or $`\exp`, have wide domains and transcendental numbers at a few stages. "Range reduction" ($`\mod \pi`) just by itself is annoying to get right and fast for all numbers.

I decided not to solve any of those problems. Instead, I really wanted to see what it would take to just do any basic floating point number theorems at all in Lean.

# My Little Theory of Floating Point Numbers

I started out by reviewing what I knew about floating point numbers:
- Each floating number had a sign bit, some mantissa, and an exponent.
- They were logarithmically spaced.
- There were special cases like -0, +0, -inf, +inf, and NaN.

Here, I knew that each floating point $`f` was something like $`f = (-1)^b (1 + m / 2^p)  2^{e}` where $`b` is a boolean, $`0 \le m < 2^{?}` , and $`e` an integer of appropriate size ($`emin \le e \le emax`).

A little research plus some remarks from a friend revealed some even more annoying special cases:
- Subnormal numbers of the form $`(m/2^p) 2^{emin}`. This one was actually very annoying to find a simple description of. The binary representation hides this simple formula!
- There's many kinds of NaNs. I elected to ignore this and assume a single NaN.
- Rounding modes
- Definition of $`+, -, *, /`. I was pleasantly surprised to learn that these are defined as "the correctly rounded exact value".

## [Flocq](https://flocq.gitlabpages.inria.fr/)

I also looked at floating point numbers in Rocq (AKA Coq) and found [`flocq`](https://flocq.gitlabpages.inria.fr/). I have mixed feeling about it.

### It's comprehensive

They seem to cover a bunch of cases. So many that it is unclear what the important elements of the theory are.

### It feels reductive

It didn't go into the details of [IEEE 754](https://en.wikipedia.org/wiki/IEEE_754). It models reals as a subset of the real numbers, which doesn't cover the special cases I care about. This makes it both noncomputable, and doesn't say anything about the `Float` datatype.

### It gave me some unhelpful ideas

After reading the "Flocq in a nutshell", I thought that the spacing would be the most important part, when to me, it seems like it's the rounding.

### It gave me helpful ideas

The idea that floats are really a bunch of evenly spaced numbers was quite instructive.

### Is it a skill issue?

I may not have traversed the library enough, but I also was struggling, because my knowledge of Rocq/Coq is not nearly as good as Lean.

## [Mathlib.Data.FP](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/FP/Basic.html)

I didn't learn about this until a few aborted attempts. I used maybe 5 definitions from this and deleted the rest. I suspect it was written before the development of `Int.log` machinery. I only learned about this from searching mathlib for more and more terms.

It seemed the most aligned with what I wanted to do though--a good sign!

### Other Lean attempts at floating point numbers

I know of the [interval](https://github.com/girving/interval) package now, but I didn't know then. Luckily it looks related but quite different in goals. I recall seeing another attempt more recently, but I cannot find it now. The whims of search are fickle indeed.

### General Floating Point Number Resources

There are some IEEE visualizers like https://lukaskollmer.de/ieee-754-visualizer/ and https://www.h-schmidt.net/FloatConverter/IEEE754.html.

## Flean Design

```leanInit demo
-- This block initializes a Lean context
```

Flean focuses on rounding from $`\mathbb{Q}` to floating point representations and interpreting floating point representations in $`\mathbb{Q}`. The use of $`\mathbb{Q}` made it all computable, and the explicit conversion functions have a lot of structure in them.

- `FloatCfg` usually named $`C` contains details of the precision `C.prec`, which is our spacing $`2^p`, which scales the mantissa. It also has `emin` and `emax` for the exponent limits. And some lemmas about these variables.
- `FloatRep` represents "normal" numbers as sign, exponent, and mantissa, so coercion to the rationals is given by $`(-1)^b (1 + m / C.prec) 2^e`. It's just a struct with 3 elements!
- `SubnormRep` represents "subnormal" numbers of the form $`(-1)^b (m / C.prec) 2^{C.emin}`. Since it's just a struct, both `(true, 0)` and `(false, 0)` represent $`0`. These are essentially small fixed point numbers right at the bottom of the range.
- `Flean.Float` which packages a `FloatRep`, `SubnormRep`, $`\pm` `inf`, `NaN` with proofs about sizes.

I also had some initial theorems I wanted to prove:

- Coercing a float to the rationals and then rounding should always give the same thing! So we have a little invertibility still.
- Rounding and then coercing back to the rationals should leave us "close" to where we started.


Writing conversion functions from representations to the rationals was extremely straight-forward. Writing the rounding function was a lot more annoying. To do `Flean.Float`, you have to first do normal and subnormal numbers.

### Normal Numbers

Once I had the integer logarithm function, getting the exponent $`e = \lfloor \log_2 |q| \rfloor` and mantissa $`m` were easy enough for rounding to 0:
$$`\lfloor (|q| / 2^{\lfloor \log_2 |q| \rfloor} - 1) \, C.prec \rfloor`
This proved sufficient for some initial theorems, but I eventually outgrew this, but you can see how the use of integer logarithms along with a lot of conversions to integers and then natural numbers.

Just proving all the theorems for injectivity required far more effort than I expected. I didn't even recognize that rounding wasn't well-defined at $`0`. There is nothing truly surprising here (i.e. nothing worth including in mathlib), but I'll leave the reader to contemplate how long it took humans to use [scientific notation](https://hsm.stackexchange.com/questions/15929/seeking-comprehensive-references-on-the-history-of-scientific-notation). The uniqueness and properties require knowing a thing or two about exponents.

I do wonder how the human computers of old would handle rounding errors. I'm more convinced
that could gradually appear if a computation was spread between several people.

### Rounding Modes

Since no one truly uses round to $`0` in a real computation, I wanted to represent the _real_ way people round floating point numbers:
- Round to nearest, but...
- If tie, then round to one with an even mantissa.

To no surprise, I had to implement this round to nearest. I eventually realized that all the different rounding modes can be represented as functions $`r : Bool \times \mathbb{Q} \to \mathbb{N}`. The boolean allows you to round to 0 or to round down, and the natural number output captures the absolute value business I had before. These `IntRounder` are a `ValidRounder` if they preserve the order of positive $`q \in Q` and if they preserve the natural numbers.

## Order properties!

TLDR: **Preserving order** and **injectivity** (with the exceptions) are how you prove properties about all floating point number calculations.

After handling a few "closeness" limits as well as trying to prove a preliminary range lemma, I realized that rounding had another property. Rounding preserves the order of numbers.

This is probably the key theorem about all the floating point representations. It gives you injectivity and closeness once you have the spacing of numbers, and it's crucial for working with ranges of floating point numbers. It's what makes interval arithmetic even work at all, once you know rounding down and rounding up bounds a value.

Assigning order properties to $`r : Bool \times \mathbb{Q} \to \mathbb{N}` allows you to lift those to the full floating point representation.

As part of my proofs, I had to define a few ways of comparing floating point numbers in a compatible way with coercion to rationals, which really used the limits of sizing. This is one of the times where it occurred to me that comparing numbers in scientific notation is not 100% trivial.

## More special cases :(

### Zero or non-zero

Many theorems about uniqueness only work for non-zero values. Either rounding isn't well defined for scientific notation, or there's $`\pm` for fixed point subnormal numbers.

### Sign bit

Positive and negative require `neg` functions and symmetries everywhere. This includes even the `IntRounder` which has its own negative version.

The only time this became truly annoying was when trying to prove that rounding preserves order, since that requires splitting into a few symmetry based cases.

### Mantissa carry-over

Some rounding modes required normalizing, but noticing that the interpreted $`\mathbb{Q}` was equivalent to an unnormalized form made most theorems simple again.

### Normal vs Subnormal

Subnormal numbers use the same `IntRounder` as normal numbers, but they are basically fixed point numbers and are much easier to deal with. The same order properties apply.

### Finite vs Otherwise

Since Float can be finite, inf, or NaN, it's necessary to specify `f.IsFinite` quite often. However, splitting `f.IsFinite` is actually a really bad idea!

It was usually more helpful to recognize that `to_rat f` was either equal to a normal `FloatRep` or to a `SubnormRep` of appropriate sizes. At the boundary, where rounding modes get things real funky, the overlap between `SubnormRep`, `FloatRep`, and that rounding preserves order made this all work out. This makes it a bit more finicky than I expected.

Coming up with the right way to split `IsFinite` took me several tries to get a nice clear theorem.

## Some other useful theorems

- Exponent-comparison determines sizes.
- Small enough rationals round to finite values.
- Error for rational numbers is quite small for all rounding modes.
- Rounding up is larger than your original value (and analogously for down).
- Rounding creates bounded mantissa for all rounding modes.
- Round-to-nearest has half the error as normal rounding modes.

At this point, I started getting real tired and decided to call it quits.

## Was verification helpful?

One little anecdote: When I was proving these theorems about floating point numbers, I actually realized that I had implemented it incorrectly at first. When implementing carry over for subnormal to normal numbers, I had an off by one error. This eventually shook out in the proof. I think that this should not be taken as evidence that formalizing numbers is an efficient way to figure out errors, since I really only got rid of one error this way.

I have run a few test cases with numbers in different sizes, like 2e-1026, or like 2e-30, and a few other variations, but I have not really systematically tested it, so who knows? Maybe it's still broken in some way.

But at least I know the theorems are true!

## Is it ready for Mathlib?

I'm not sure. I have not included a linter or done documentation. There are some concerns I have still with how I implemented it.

- Should configuration be a type class?
- Should precision be a power of two?
- Is it better to represent all of them like $`m 2^n` instead? This might better unify the representations, better reflect the literature (like [here](https://inria.hal.science/inria-00070603/file/BolMel.pdf)), and better work with recursive reals or something.
- Is there a simpler way to do things?

## What is the purpose of it again?

Personally, I found it quite useful as an exercise. And I think that if I was going to do future work involving floating point numbers, I would try to abstract a lot of my current theorems as an interface that you can just assert axiomatically over opaque types.

If I had to actually prove that a specific floating point number computation is correct, I would rather use an interval arithmetic library.

When I started going for this, I immediately started thinking of applications. The error approximation theorems could be used to prove correctness of longer computations.

But computationally, I really wouldn't want to do things this way, because you have to have all these different ranges involved throughout the query. Maybe there are ways to propagate range information backwards through a computation, so a finite output is enough to guarantee good results. Overall that seems like a lot of work.

Essentially, I might want to answer the question, for what domains should you expect good errors? But this doesn't seem to have good answers uniformly. You should expect catastrophic cancellation when you have large positive and large negative numbers of roughly equal size. And this can happen just for a vector-vector multiplication. Applications seem to always need to mix relative and absolute error in really annoying ways, while invoking bounds on the sizes.

Or you can just use specific intervals and work with those.

# What I hated about this

- How many special cases there are
	It felt like I really couldn't do anything without having at least two cases, and sometimes four, and sometimes like six. Not fun.

	It was probably good for me, though, because it required me to figure out how to refactor things so it's not the most horrible. Although, I could probably improve that.
- Weird junk values
	I think I've gotten used to them.
- So many caveats...
- Basic algebra bashing is still very annoying in lean. It doesn't seem to be very reusable at all either.

I don't really want to develop this theory anymore. It's sort of exhausting, and I feel like if I broaden my horizons, I can learn a lot more. Maybe I'll go to recursive reals instead.


# Leaning Lean as a Language

I wanted to specifically learn the kind of basic theory I figured would be involved in applied mathematics.

Going into this, I had read through the [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/) documentation, which I found to be very interesting and a lot more intriguing than the [beginner Coq documentation](https://softwarefoundations.cis.upenn.edu/). There was a lot of basic things I still had to learn--sometimes quite painfully. Perhaps the most important example would be the tactic `exact?` which tells you the answer sometimes. It's obviously incredibly useful, but perhaps dangerous for some users.

## Searching for a theorem

When I actually wanted to start coding a function to go from rationals $`\mathbb{Q}` to floating point numbers, I wanted a function that computed $`\lfloor \log_2{|q|} \rfloor`. There are several ways to accomplish this. At the time, I thought that I would use `Int.floor`, which I knew existed, and `Real.log`, which I was pretty sure existed as well. Pretty quickly, I realized I didn't actually like that solution. $`\mathbb{R}` is noncomputable, which was very unappealing.

I started writing my own function to do a logarithm because I couldn't figure out what kind of logarithm I wanted to write. I knew about `Nat.log` too, but I didn't want that exactly either. My own implementation had a few of my own false starts (which I could have avoided with pen and paper), but eventually I figured out the **right** search terms. I was trolling through the files related to `zpow` and realized that there was an `Int.log` with a definition essentially identical to mine. After experiencing this, I realized that my usual go-to of googling is a terrible way to learn a theory in Lean. Instead,

+ Try searching in mathlib documentation. You may need to scroll a lot.
+ Try searching for a theorem name with `exact?`.
+ Try searching with [leansearch.net](leansearch.net) or with `#leansearch`. Despite being AI, the hype for leansearch is real. There's also Moogle, but I never use it.
+ Search for theorems you might think are related to your function.
+ Try searching zulip manually. Zulip is not typically indexed by Google.

Once I found the right theory for integer logarithms and powers, the rest of the theorems I needed were easy enough. I learned a lot just by reading definitions and associated proofs in those files. I was really cooking now.

Ultimately, it seems impossible to keep all of the theorems necessary in memory. Unless the programming magically becomes more expressive, tactics become more powerful, or something like that, it seems like something like leansearch is the future + exact? of course. I wouldn't discount future magical changes in Lean though.

## Real-world tactics

There's also a variety of tactics that you'll see used in Lean code that I did not really use in the beginner documentation. I systematically went through all the tactics eventually and figured out what they actually did. Mathematics in Lean doesn't tell you about `refine`. And `refine` is extremely important, because it shows up all the time in actual code. There's some other features that the documentation tells you about, like substituting with `rfl` in calls to `rcases` or other tactics. Unfortunately, this never worked because `rfl` doesn't do rewriting beyond single variables. Similarly, things like `apply_fun`, which is a tactic that should apply a function to both sides of an equation, was extremely flaky and I couldn't get it to work in a single real proof.

## Positivity

Other tactics were indispensable, and I took a while to find them. For instance, `positivity`. `positivity` is a tactic that proves whether a quantity is positive. That can actually include non-negative, include non-zero, and it can just be straight up positive. I thought, this is the bee's knees.

Since a lot of theorems in `mathlib` generally, and specifically floating point numbers, involve proving that certain quantities, positive or non-negative or non-zero, just so you can divide and cancel things, it ends up being essentially indispensable. When you write your own functions or more complicated expressions, you can also extend the tactic in a way that `positivity` will apply to it. This is very important because it can save you time in way more cases, even when you aren't calling `positivity` yourself.

That said, you seem to only be able to extend `positivity` calls for function calls and not general pattern matching like `simp`. Often times, I identified key expressions that needed to be positive, such as part of the mantissa `|q| / 2^Int.log |q| - 1`, but I ended up using a function instead, which was far less convenient. I am not sure how users are even supposed to find strange positivity lemmas like this anyways.

If I had to redo everything, I would actually factor more complicated expressions into functions that I can then prove positivity constraints about.

In a similar vein, `gcongr` looks like another excellent tactic here!

## Simplifier and Normalization Tactics

Tactics such as `group`, `ring`, `field_simp` I knew about from the Mathematics in Lean documentation, but I found them to not be very effective. They were intended to finish proofs and not really simplify them.

Most of my time was spent figuring out how to either get to a place where a group or ring could do its job, or to figure out how to do the last manipulation so that `field_simp` would actually do something useful.

Some tactics I discovered later were a lot more helpful than I thought at first. The `simp?` tactic is a great way to make partial progress in a predictable way. The other tactic I found to be helpful in a very late stage was `omega`, which lets you prove general facts about integers. Since most of what I was doing involved rational numbers, it wasn't as effective, which is a little bit surprising because I would expect that rational numbers and integers to be extremely similar.

On the normalization side, `norm_cast`, `qify`, and `zify` were very helpful since there is a lot of casting between natural numbers, integers, and rationals. I learned about these when I tried to prove that $`\sqrt{2}` is irrational via $`\neg \exists q \in \mathbb{Q}, q^2 = 2`. Just doing that was quite an exercise since it is not straightforward how to do anything with rationals in Lean.

## Tactics I didn't figure out how to use

There are some tactics I think might be a lot more helpful, but I really didn't know how to use effectively.

1. `aesop`: As a general solver, it can probably do a lot more, but the configuration seemed challenging, and I didn't know how to get started. It's not useful by default it seems.
2. Custom `simp` lemmas: It's unclear what should be a simp lemma and when you should just pass your lemma to simp with `simp [your_lemma]`, so that's usually what I did instead.
3. [`bound`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Bound.html) : which seems like it should do almost exactly what I want a lot, but I never actually found a specific scenario in which it worked. This may be user error.

## "Without Loss of Generality" tactic

I have been avoiding this one. I have mixed feelings about it. In some ways, it lets you clear out specific cases very quickly, but it often hides the higher order logic. `wlog` lets you assert a statement and then you can prove that its negation still lets you prove the theorem somehow. However, this often obscures some symmetry arguments that are useful to extract out as their own lemmas or pseudo-induction theorems.

As an example, I often had to deal with both a positive and negative case. I started out by using `wlog`, but it's cleaner to define `neg` functions on the representations and a set of theorems there. Similarly, I created a theorem to apply symmetry arguments on the rationals to prove theorems of the type `P q1 q2`.

## Splitting tactics I'm unsure about

`split_ifs`, `split`, `match`, and `if` can all be used to split theorems into special cases either defined by users or defined by the goal of a proof instead. I have no idea which one is the "best" to use at any given time. They all seem to have their own gotchas in terms of manual work and labeling hypotheses.

Sometimes I also discovered that the way you split a function or a function definition is counterproductive to how you want to split a theorem into pieces. Again, it's usually best to define your own way to split hypotheses and goals as their own lemmas.

## General proof structure

I also learned about the how to structure proofs outside of these symmetry / higher-order methods. There's a lot more use of `apply`, `have`, and `suffices` than I thought. I would say 90% of the effort is writing out what I need in either one of them. Sometimes, it trivially matches what I would write in $`\LaTeX`, but other times, it requires a bit of finagling with `suffices`. I'm not disappointed at all here; it was mainly a matter of practice.

## Named Arguments

As a new features in Lean 4, the standard library doesn't use this much, and in fact, the documentation is pretty light on its usage too. I found it to be one of the most helpful features, and I will deeply miss it in any functional programming language from now on.

When you define a lemma in lean, you typically make any variables that can be inferred from later theorems as implicit with `{q : Rat}`. However, this does not help you when you are applying _backwards reasoning_. The standard approach in the documentation is to specify what you are missing with `@lemma_name _ _ _ q` or however many `_` you need for the other inferred variables. With named arguments, you can do `lemma_name (q := q)`.

The only downside is that too many theorems do not have meaningful names for hypotheses. If there is only one, then it's `h`, otherwise ¯\\\_(ツ)\_/¯.
### Things I didn't learn but expected to

- What's the best way to write readable Lean code?
	- Should I be using `show` more?
	- I definitely should be using more comments.
- How do you make your library easy to use, easy to understand, and extensible?
- Should I be using type class inference or implicit variables?
	I went back and forth on this very often, and currently think I should have gone with type classes for floating point parameters like precision or maximum exponent.

	If I'd known about named arguments for type classes, it would have changed my decision as well. I recall having problems with specifying the parameters in an inductive theorem, but that was probably a skill issue.

## Things I knew but didn't want to believe

You should write your theorems out on paper first, and you will be forced into more generality eventually.

Everything is more complicated than you expect. Approaching a theorem from scratch, it felt very difficult to get a lot of traction on it because everything felt obvious. As I went on, I discovered the most important factors of a piece, and I'd have to refactor my system to work in more general settings just so I can get new rounding codes. And I'd have to think about what are the elements that are most important, the things that would let me use `mathlib` to the greatest effect.

# Thoughts about Lean in General

There's this little aphorism I repeat to myself: to solve your problem, first solve first order logic. I feel like that applies here too. The existing tactics and language features still feel vaguely incomplete. I think there's even a lot of low-hanging fruit here too, maybe on the software engineering side of defining tactics.

Some counterexamples of "bad" tactics also astound me. `apply?`doesn't return useful searches even with the `using` keyword. Similarly, `conv?` often fails when the expressions become too complicated to select.

There are some general features of tactics I've really grown to appreciate:
- Good tactics return partial progress like `simp`
- Good tactics let you inspect and modify search like `simp?`
- Good tactics let you cache search and see small proof outputs also like `simp?`.
- Good tactics are extensible like `positivity`.
- Good tactics play nicely with other tactics like `gcongr`.

Ultimately, I expect tactics to rarely "solve" everything. For every tool, there is a problem it cannot solve. Not every tool needs to completely decide a problem, so it's important to return partial progress and allow users to pick up where tools leave off, expanding the set of decidable problems.
