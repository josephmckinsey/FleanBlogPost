import FleanBlogPost.Page
import Flean

set_option pp.rawOnError true

open Verso.Output.Html in
def ieee754converter : Verso.Output.Html := {{
  <video width="75%" controls="true" style="max-width: 75%; margin: 0 auto; display: block;">
  <source src="flean/ieee754converter.webm" type="video/webm"></source>
  "This is demonstration of how the IEEE 754 visualizer works by showing a small
  number like 0.00001 and then a really small subnormal number along with some
  multiples of them"
  </video>
}}

open Verso.Output.Html in
def type_diagram : Verso.Output.Html := Verso.Output.Html.tag "img" #[
  ("src", "flean/type_diagram.svg"),
  ("alt", "A diagram showing the different types of floating point numbers in Flean"),
  ("style", "max-width: 50%; margin: 0 auto; display: block;")
] (.text false "")

open Verso.Output.Html in
def float_diagram : Verso.Output.Html := Verso.Output.Html.tag "img" #[
  ("src", "flean/float_diagram.svg"),
  ("alt", "A diagram of the types on a number line"),
  ("style", "max-width: 50%; margin: 0 auto; display: block;")
] (.text false "")



#doc (Page) "Flean: Floating point numbers in Lean, mostly done!" =>
> Note: this probably won't make sense to anyone who hasn't tried to learn the
language [Lean](https://lean-lang.org/) yet. Do it! There's a [Lean 4 game about
formalizing natural numbers](https://adam.math.hhu.de/), which is quite
approachable.

TLDR: Implementing floating point numbers in Lean taught me a lot about floating
point numbers. It sharpened my thinking, helped me learn more mathematics in
Lean, and it helped me understand rounding as a concept.

# {label intro}[Introduction]

See my previous post on [Flean](https://josephmckinsey.com/flean.html) for
background on why I decided to do this.  Now that I've gotten many of my "goal"
theorems, I felt it was a good time to share what I did and learned. {ref approaches}[First],
I'll go through some of the more basic theory and existing
lines of work in formalization. This should be accessible to anyone who has a
mild familiarity with them already. {ref design}[Next], I'll go through the
design of the library I created, `Flean`. This will be slightly more technical,
but I won't go through any code snippets in detail. {ref leanlanguage}[Finally],
I'll go through my own experience with learning Lean as a language, describing
what some of the fundamentals I learned about the language. This is geared
towards someone who has some familiarity with the beginner documentation of
Lean, so I expect you to know what tactics are.

Floating point number errors can be quite subtle, and they
explode when subtracting two large yet
nearly equal numbers followed by multiplication
or division. If you are not careful, you can easily invalidate your results.
Large portions of the 20th century numerical analysis literature
weeded out "unstable" algorithms in favor of largely trusted code,
but many common functions still have more errors across wider ranges
than you would guess. Even `sin` is not perfectly accurate on all platforms,
let alone something like matrix inversion. Theorems about floating point numbers
can sharpen our understanding, but they can also provide certificates
that a function is actually "good enough". Usually if you mess up, the worst
that happens is NaN, but sometimes it's more like
[missile malfunctions](https://www-users.cse.umn.edu/~arnold/disasters/patriot.html).

Since I won't be going through my code in significant detail, if you want
to truly understand how it works, then unfortunately the
[code](https://github.com/josephmckinsey/Flean.git) is still the best option,
and I still haven't learned how to really write documentation in Lean yet.
If you were looking for practical applications, then keep looking, but
maybe I'll invest more if interest arrives. That said, there are certainly
possible applications, but mainly they boil down to proving that calculations
done with floats are "close" to the true answer done with real numbers.

# {label approaches}[Approaches for Floating Point Number Proofs]

Typically, there are two ways you prove facts about floating point number
errors in a theorem-proving language. Either you use interval arithmetic
to bound calculations, or you bound the error more loosely with each operation.

Interval arithmetic is better at tight bounds and chaining computations, since
it packages error propagation generally with the rounding to floats. There are
also more extensions for correlating error across computations. You also don't
need to prove anything about conditions of your floating point number, since you
get a bound for your specific input. That's really convenient for arbitrary
computations.

More traditional numerical analysis models each operation as introducing some
absolute or relative error, which can be propagated into other errors as numbers
are added or multiplied. This becomes quite annoying when you have to mix
absolute and relative error, which is often, and long running computations can
produce extremely loose and large error bounds.

Finally, SMT solvers may be the fastest way to prove facts about floating point
numbers as well. For the uninitiated, satisfiability modulo theories (SMT) solve
satisfiability problems (like 'is this formula satisfied for a choice of
variables?') modulo a theory like "real numbers" or "bitwise arithmetic" (see
[`bv_decide`](https://leanprover-community.github.io/mathlib4_docs/Lean/Elab/Tactic/BVDecide.html)).
Since floating point computations can be reduced to bitwise arithmetic, this may
be a better long-term approach for proving facts about floating point numbers. I
have not investigated as much as I should, but my impression is that theorems do
not translate as well to different floating point number types (64-bit vs
32-bit).

Creating functions with small errors is also extremely tricky. Many common
functions such as $`\sin` or $`\exp`, have wide domains and transcendental
numbers at a few stages. "Range reduction" ($`\mod \pi`) just by itself is
annoying to get right and fast for all numbers. You end up needing
to use many digits of pi, and representing that in a way you can apply with
just floating point numbers is not trivial.

I decided not to solve any of those problems. Instead, I really wanted to see
what it would take to just do any basic floating point number theorems at all in
Lean. Maybe later I'd try to build upon this with accurate computations.  Next,
I'll walk you through how I designed and implemented a theory of floating point
numbers in Lean. Floating point number are a very well-studied topic both within
and outside formalized mathematics, so there were many resources to help guide
me. I'd like to think I put my own spin on things.


## {label theory}[A broad overview of floating point numbers]

I started out by reviewing what I knew about floating point numbers:
- Each floating number had a sign bit, some mantissa, and an exponent.
- They were logarithmically spaced.
- There were special cases like -0, +0, -inf, +inf, and NaN.

Here, I knew that each floating point $`f` was something like $`f = (-1)^b (1 +
m / 2^p)  2^{e}` where $`b` is a boolean, $`0 \le m < 2^{?}` , and $`e` an
integer of appropriate size ($`emin \le e \le emax`). These formulas
were easy to figure out from either Wikipedia, my college memories,
or the books of numerical analysis I've perused over my life and for this
project.

A little more research into the details of [IEEE 754](https://en.wikipedia.org/wiki/IEEE_754)
plus some remarks from a friend revealed some even more annoying special cases:
- Subnormal numbers of the form $`(m/2^p) 2^{emin}`. This one was actually
very annoying to find a simple description of. The binary representation
hides this simple formula!
- There's many kinds of NaNs. I elected to ignore this and assume a single NaN.
- Rounding modes. By default, the default rounding mode is round-to-nearest + special cases,
but it's useful to have other rounding modes. These alternate modes help motivate more
generality too.

The [IEEE 754](https://en.wikipedia.org/wiki/IEEE_754) standard is not without
pleasant surprises. The basic arithmetic operations $`+, -, *, /` are defined
as the correctly rounded exact values. As long as I was careful about computability,
I didn't even need to write custom $`+, -, *, /`, etc implementations. All you
need is rounding.

Even knowing the details and understanding it, the structure and design of the
theorems remains. This is where formalization differentiates itself, since you
now need to organize all the facts around a simpler set of rules you
can start with.

## [Flocq](https://flocq.gitlabpages.inria.fr/)

I also looked at floating point numbers in Rocq (AKA Coq) and found
[`flocq`](https://flocq.gitlabpages.inria.fr/). I have mixed feelings about it
as a design for Lean. On one hand, it's quite comprehensive. They cover
many cases and extensions that I didn't really consider. In fact, it was
hard to determine a unifying theme for all of it. I'd also consider
it somewhat oversimplified by default. It didn't go into the details of
[IEEE 754](https://en.wikipedia.org/wiki/IEEE_754). It models floating point
numbers as a subset of the real numbers, which doesn't cover the special
cases I care about (like $`\pm`). This makes it both noncomputable and
doesn't say anything about the `Float` datatype. There may be a way to
get around this by quotient types, but I thought there was a better way.

Based on the page "Flocq in a nutshell", I thought that spacing
between floating point numbers would be far more important than
anything else. The way I approached it, rounding seemed like the
more fundamental principle. It was very helpful to think of the
floating point numbers as sets of evenly spaced intervals for each
exponent.

That said, I would take my own criticisms with a grain of salt. I am
not nearly as knowledgeable about Rocq's libraries as I am of Lean.
It could be skill issue, and the library does really handle "real"
floating point numbers via some indirection. I wanted to handle
those "real" floating point numbers more directly. This is around
the time I thought I could do it with a comparison to $`\mathbb{Q}`,
which is very much computable and easier to work with than $`\mathbb{R}`.

## [Mathlib.Data.FP](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/FP/Basic.html)

After a few aborted attempts at trying to figure out configuration, rounding,
and how to work with rationals, I found the existing attempt at floating point
formalization at `Mathlib.Data.FP`. I used maybe 5 definitions from this and
deleted the rest. I suspect it was written before the development of `Int.log`
machinery, which is far too convenient to ignore. I only learned about this from
searching mathlib for more and more terms. It also seemed the most aligned with
what I wanted to do though--a good sign!  I am quite indebted to
`Mathlib.Data.FP` as otherwise, I would have spent longer having to write the
configuration objects.

## Other Lean attempts at floating point numbers

I know of the [interval](https://github.com/girving/interval) package now, but I
didn't know until quite far into my own attempts. Luckily it looks related but
quite different in goals. I recall seeing another attempt more recently, but I
cannot find it now. The whims of search are fickle indeed.

## General Floating Point Number Resources

Every so often, more modern explanations easily outstrip old ones. Nowadays,
there are modern visualizers of the bit-layout of floating point numbers. You
can plug in different bits and easily see what number is produced.  I really
like https://lukaskollmer.de/ieee-754-visualizer/ and
https://www.h-schmidt.net/FloatConverter/IEEE754.html. I wish I'd been shown
these years ago! Bit twiddling in Python or C++ is not nearly as convenient.

::::blob ieee754converter
::::

At this point, I decided to "send it" and just try coding some basic structures
and functions around it. In the next section, I'll go into the design I landed
on for `Flean`.

# {label design}[Flean Design]

```leanInit demo
-- This block initializes a Lean context
```

Flean focuses on rounding from $`\mathbb{Q}` to floating point representations
and interpreting floating point representations in $`\mathbb{Q}`. The use of
$`\mathbb{Q}` made it all computable, and the explicit conversion functions have
a lot of structure in them. Since the behavior of floating point numbers is completely
determined by the rounding, this provides a pretty good base to build more
complicated proofs off of (hopefully).

Here are a few core data types the library is proving things _about_:

::::blob type_diagram
::::

- `FloatCfg`: usually named $`C` contains the precision `C.prec`,
which is the density of points for each mantissa. It's usually $`2^p` and scales the mantissa.
`FloatCfg` also has `emin` and `emax` for the exponent limits. And some lemmas about these variables.

```lean demo
def DoubleCfg : FloatCfg := FloatCfg.mk (1 <<< 52) (-1022) 1023 (by norm_num) (
  Nat.zero_lt_succ 4503599627370495  -- computed with exact?
)  -- this is a double
```

- `FloatRep` represents "normal" numbers as sign, exponent, and mantissa, so
coercion to the rationals is given by $`(-1)^b (1 + m / C.prec) 2^e`. It's just
a struct with 3 elements!

```lean demo
def example_normal : FloatRep DoubleCfg := FloatRep.mk false 0 23
-- Converting to rational, it's just a bit bigger than 1
#eval coe_q example_normal  -- Try hovering or clicking terms
```

- `SubnormRep` represents "subnormal" numbers of the form $`(-1)^b
\frac{m}{C.prec} 2^{C.emin}`. Since it's just a struct, both `(true, 0)` and
`(false, 0)` represent $`0`. These are essentially small fixed point numbers
right at the bottom of the range of "normal numbers".

```lean demo
def example_subnorm : SubnormRep DoubleCfg := SubnormRep.mk false 10
#eval subnormal_to_q example_subnorm  -- Converting to rational, it's really close to 0
```

- `Flean.Float` which packages a `FloatRep`, `SubnormRep`, $`\pm` `inf`, `NaN`
with proofs about sizes. I haven't proved this, but there should be a bijective
correspondence between ordinary floating point numbers and these `Flean.Float`.

```lean demo
def example_float : Flean.Float DoubleCfg := (Flean.Float.normal
  example_normal
  (by simp [FloatRep.valid_e, example_normal, DoubleCfg])
  (by simp [FloatRep.valid_m, example_normal, DoubleCfg]))
#eval to_rat example_float  -- Converting to rational, it's just a bit bigger than 1
```

::::blob float_diagram
::::

Here are the "goal theorems" I really wanted to prove (and succeeded):

- Coercing a float to the rationals and then rounding should always give the
same thing! So we have a little invertibility still. This limited "injectivity"
of the floating points into the rationals captures how floating point numbers
are a subset of the rationals.

```lean demo
#check to_float_to_rat
```

- Rounding and then coercing back to the rationals should leave us "close" to
where we started.

```lean demo
#check float_error
```

Writing conversion functions from the floating-point representations to the
rationals was extremely straight-forward. Writing the rounding function was
a lot more annoying. To do `Flean.Float`, you have to first do normal and
subnormal numbers.

## Normal Numbers

Once I had the integer logarithm function in hand, getting the exponent $`e =
\lfloor \log_2 |q| \rfloor` and mantissa $`m` were easy enough when rounding to
0:

$$`\lfloor (|q| / 2^{\lfloor \log_2 |q| \rfloor} - 1) \, C.prec \rfloor`

This proved sufficient for some initial theorems and exploration, but I
eventually outgrew this when I wanted to talk about other rounding modes.
You can already see how the use of integer logarithms along
with a lot of conversions to integers and then natural numbers.

Just proving all the theorems for injectivity required far more effort than I
expected. I didn't even recognize that rounding wasn't well-defined at $`0`.
There is nothing truly new foundationally here (i.e. nothing worth including in
mathlib), but I'll leave the reader to contemplate how long it took humans to
use [scientific notation](https://hsm.stackexchange.com/questions/15929/seeking-comprehensive-references-on-the-history-of-scientific-notation).
The uniqueness and properties require knowing a thing or two about exponents.
Today, it should fall out of basic algebra.

I do wonder how the human computers of old would handle rounding errors. I'm
more convinced that subtle rounding errors could gradually appear if a
computation was spread between several people.

## Rounding Modes

Since no one truly uses round to $`0` in a real computation, I wanted to
represent the _real_ way people round floating point numbers:

- Round to nearest, but...
- If tie, then round to one with an even mantissa.

To no surprise, I had to implement this round to nearest. This is significantly
more annoying than just flooring, but like flooring, we can do it with special
function. I eventually realized that all the different rounding modes can be
represented as functions $`r : Bool \times \mathbb{Q} \to \mathbb{N}`. The
boolean allows you to round to 0 or to round down, and the natural number output
captures the absolute value business I need for a non-negative mantissa. These
`IntRounder` are a `ValidRounder` if they preserve the order of positive $`q \in
Q` and if they preserve the natural numbers.

Here are the key functions and lemmas:

```lean demo
#print round_near_int
#check ValidRounder.le_iff_le
#check ValidRounder.leftInverse
```

## Order properties!

TLDR: **Preserving order** and **injectivity** (with the exceptions) are how you
prove most properties about all floating point number calculations.

After handling a few approximation lemmas as well as trying to prove a preliminary
range lemma, I realized that rounding had another really important property beyond
injectivity and approximated error. Rounding preserves the order of numbers.
If you want to prove that "all numbers in this range round to within another range",
then using the ordering provides you much tighter bounds. You can just compute
the behavior at the boundary and extrapolate.

You don't necessarily _need_ that rounding preserves order. For instance,
it still seems clear to me that a version of rounding that added
more noise would still have some of the same convenient properties, but
you wouldn't be able to prove theorems and lemmas nearly as directly.
Preserving order lets you compare floating point numbers and rationals as if they
live in the same space, so $`x \le \sqrt{2}` implies that $`\mathrm{r}(x) \le \sqrt{2}`,
which is very convenient.
Preserving order and injectivity gives you lemmas about closeness once you can find and use
nearby floating point numbers. Note that this comparison uses $`\le` and not $`<`,
since $`x < 1` may leave us with $`\mathrm{r}(x) = 1`.

Preserving the ordering also proves that
interval arithmetic works at all, once you know rounding down and rounding
up bounds a value. If you wanted to use `Flean` to develop a theory of interval arithmetic,
then you would start with the facts that the rounding modes bound $`x`:
$`x^- \le x \le x^+`. Then you can prove theorems like $`(x^- + y^-) \le x + y \le (x^+ + y^+)`
using the usual properties of rationals, then finally we can apply rounding one more time:
$`(x^- + y^-)^- \le x + y \le (x^+ + y^+)^+`. Since IEEE754 defines addition
of floating point numbers using rounding like this, we can then prove
that the true answer $`x + y` is within these bounds. Assuming you are willing
to fiddle with CPU rounding modes, then you have some verified bounds
on computations. That said, it may be more convenient to replace rounding up
to $`x^+` with "rounding + a small constant" instead.

Proving the rounding properties is also simple enough with our convenient
`ValidRounder.le_iff_le` lemma. Rounding on the rationals is a scaled version of
the integer rounder rounder $`r : Bool \times \mathbb{Q} \to \mathbb{N}`.
There's a few caveats in positive or negative and normalization, but it's
nothing serious.

I initially defined the comparison of floating point numbers using the
"injection" to the rationals, but for computing comparisons to specific values
such as $`2^e`, it was convenient to define a direct comparison.  There are a
couple ways of doing this once numbers are normalized, either by looking for
exponent differences and then mantissa differences.  This is one of the several
times where it occurred to me that comparing numbers in scientific notation is
not 100% trivial. I'll leave it to your imagination to create scenarios where
insufficient normalization could make the comparison annoying.

```lean demo
#print floatrep_le_pos  -- nice
#print floatrep_le_pos'  -- nice equivalent form
#print floatrep_le  -- I try to avoid this because of the casework
#check floatrep_le_iff_coe_q_le  -- a "goal theorem"
```

## More special cases :(

If I was pleasantly surprised by how nice order-theoretic properties simplified
the proofs, I was unpleasantly surprised by how many special cases there were.
I expected a few, but I had hoped that I could have squished more of them together
somehow.

What actually happened was that each time I encountered a special case,
I either needed special hypotheses and lemmas, symmetry laws to
reduce the cases, or equivalent representations to provide more
convenient forms. Splitting more naively was usually a stop-gap
solution. I'll go through a few of the special cases one by one and show
how I tackled them.

### Zero or non-zero

Many theorems about uniqueness or injectivity only work for non-zero values.
Either rounding isn't well defined for "normal" numbers at $`0`, or there's
the non-unique floating points $`\pm 0` for fixed point subnormal numbers.
This means that I often need to carry around hypotheses like $`q \neq 0`
or consider them separately:

```lean demo
#check le_roundf_of_le  -- observe a lot of nonnegativity hypotheses
```

I would consider this case unavoidable since floating point numbers
have `+0` and `-0`, which behave differently for functions like `atan2`.
That actually impacted me at my day job unfortunately.

### Sign bit

As related to the `±0` issue, the sign of a floating point number often
determines special behavior away from $`0` too. I dealt with this by
`neg` functions and symmetries laws through rounding and coercion/injection.
When rounding $`-q`, you also have to carry through a negative `IntRounder`
which mirrors rounding up to rounding down and vice versa. This application
of symmetry was so successful that I considered reframing more in terms of symmetry,
but it seemed too ad-hoc. Algebra bashing directly was more effective usually.

```lean demo
#check coe_q_of_neg -- an example of my symmetry laws
```

When proving rounding preserves order, symmetry laws became truly annoying.
As the theorem is not symmetric in each variable separately, I split
the plane $`\mathbb{Q} \times \mathbb{Q}` into 4 quadrants and created
symmetry goals for the different pieces.
The only time symmetry laws became truly annoying was when trying to prove that rounding
preserves order, since that requires splitting into a few symmetry based cases.

```lean demo
#check casesQPlane -- way too many cases here
```

### Mantissa carry-over

Some rounding modes required normalizing, but noticing that the normalized injected
$`\mathbb{Q}` was equivalent to an unnormalized form simplified expressions
when in $`\mathbb{Q}` (which I usually was).

```lean demo
#check coe_normalize
```

When I was not in $`\mathbb{Q}`, I had to deal with normalization when
it actually mattered for the sizes of the mantissa and exponent.

### Normal vs Subnormal

Subnormal numbers use the same `IntRounder` as normal numbers, but they are
basically fixed-point numbers and are much easier to deal with. The same order
properties apply.

```lean demo
#print subnormal_round
```

Although they have their own special cases, the algebra was much simpler,
and the case was interesting enough to enjoy characterizing for its own sake.

### Finite vs Otherwise

When dealing with a full "Float", there are additional cases. Since Float can
be finite, inf, or NaN, it's necessary to specify `f.IsFinite` quite often.
However, splitting `f.IsFinite` is actually a really bad idea! Naively,
the tactic `split` creates 4 cases, and blocks access to the original
float's other hypotheses if you focus on a particular case.

It was more helpful to recognize that `to_rat f` was either equal to a normal
`FloatRep` or to a `SubnormRep` of appropriate sizes (so `SubnormRep`s are the
small ones and `FloatRep` are the large ones). At the boundary between
`SubnormRep` and `FloatRep`, where rounding modes get things real funky, the
overlap between representations plus rounding preserves order smoothed out both
cases. This makes combining representations a bit finicky but definitely worth it.

```lean demo
#check splitIsFinite  -- This is how you _should_ split isFinite
```

Coming up with the right formulation for `IsFinite` took me several tries.
The first 5 or so were disgustingly unergonomic. This is perhaps
the one I'm most proud of.

## Some other useful theorems

Plowing through special cases did gift me with some neat theorems.

- Exponent-comparison determines sizes.

```lean demo
#check floatrep_e_le_of_coe_q
#print floatrep_le_pos
#print floatrep_le_pos'
```

- Small enough rationals round to finite values.

```lean demo
#check float_range
```

- Error for rational numbers is quite small for all rounding modes.

```lean demo
#check float_error
```

- Rounding up is larger than your original value (and analogously for down).

```lean demo
#check float_down_le
#check le_float_up
```

- Rounding creates bounded mantissa for all rounding modes.
- Round-to-nearest has half the error as normal rounding modes.

```lean demo
#check float_nearest_error
```

At this point, I started getting real tired and decided to call it quits.
There's always more to prove, and I'd like to do other things too.

## Was verification helpful?

One little anecdote: When I was proving these theorems about floating point
numbers, I actually realized that I had implemented it incorrectly at first.
When implementing carry-over for subnormal to normal numbers, I had an
off-by-one error. This eventually shook out in the proof. This should not be
taken as evidence that formalizing numbers is an efficient way to figure out
errors, since I really only got rid of one error this way.

I have run a few test cases with numbers in different sizes, like 2e-1026, or
like 2e-30, and a few other variations, but I have not really systematically
tested it, so who knows? Maybe my operations are still broken in some way.
But at least I know the theorems are true!

## Is it ready for Mathlib?

I'm not sure. I have not included a linter or done documentation. There are some
concerns I have still with how I implemented it.

- Should configuration be a type class?
- Should precision be a power of two?
- Is it better to represent both `FloatRep`s and `SubnormalRep` like $`m 2^n`
instead?

  This might better unify the representations, better reflect the
  literature (like
  [here](https://inria.hal.science/inria-00070603/file/BolMel.pdf)), and better
  work with recursive reals or something.

- Is there a simpler way to do things?

  This question haunts me.

## What is the purpose of it again?

Personally, I found it quite useful as an exercise. And I think that if I was
going to do future work involving floating point numbers, I would try to
abstract a lot of my current theorems as an interface that you can just assert
axiomatically over opaque types.

If I had to actually prove that a specific floating point number computation is
correct, I would rather use an interval arithmetic library.  When I started
going for this, I immediately started thinking of applications.  The error
approximation theorems could be used to prove correctness of longer
computations. But computationally, I really wouldn't want to do things this way,
because you have to have all these different ranges involved throughout the
query. Maybe there are ways to propagate range information backwards through a
computation, so a finite output is enough to guarantee good results.

Essentially, I would want to answer the question: for what domains should you
expect good errors? But this doesn't seem to have good answers uniformly. You
should expect catastrophic cancellation when you have large positive and large
negative numbers of roughly equal size. And this can happen just for a
vector-vector multiplication. Applications seem to always need to mix relative
and absolute error in really annoying ways, while invoking bounds on the sizes.
Or you can just use specific intervals and work with those. Overall,
there looks to be more fun low-hanging fruit elsewhere.

## {label hatred}[What I don't like about the design]

Despite being quite happy with my work and with the process, some
parts frustrated me to no end. I won't go into too many details here.

- How many special cases there are
	It felt like I really couldn't do anything without having at least two cases,
	and sometimes four, and sometimes like six. Not fun.

	It was probably good for me, though, because it required me to figure out how
	to refactor things so they're not as horrible. Although, I could probably
	improve that.
- Weird junk values (AKA why does `1/0 = 0`?)
	I think I've gotten used to them.
- So many caveats...
- Basic algebra bashing is still very annoying in lean. It doesn't seem to be very reusable at all either.

I don't really want to develop this theory anymore. It's sort of exhausting, and
I feel like if I broaden my horizons, I can learn a lot more. Maybe I'll go to
recursive reals instead, which have their own weird behavior.

# {label leanlanguage}[Learning Lean as a Language]

Some of my real goals were mildly independent of floating point numbers
intrinsically. I wanted to specifically learn the kind of basic theory I
figured would be involved in applied mathematics. Going into this, I had read
through the [Mathematics in
Lean](https://leanprover-community.github.io/mathematics_in_lean/)
documentation, which I found to be very interesting and a lot more intriguing
than the [beginner Coq
documentation](https://softwarefoundations.cis.upenn.edu/). There was a lot of
basic things I still had to learn--sometimes painfully. Perhaps the most
important Lean trick I learned would be the tactic `exact?` which tells you the answer
sometimes. It's obviously incredibly useful, but perhaps dangerous for
beginners to over-rely on.

Most of my reflections on Lean fundamentals fell into either
search methods, intermediate-level tactics, or general programming fundamentals.

## Searching for a theorem

When I actually wanted to start coding a function to take me from rationals
$`\mathbb{Q}` to floating point numbers, I wanted a function that computed
$`\lfloor \log_2{|q|} \rfloor`. There are several ways to accomplish this. At
the time, I thought that I would use `Int.floor`, which I knew existed, and
`Real.log`, which I was sure existed. Pretty quickly, I realized
I didn't actually like that solution. $`\mathbb{R}` is noncomputable, which was
very unappealing for things like "unit tests".

I started writing my own function to do a logarithm because I couldn't figure
out what kind of logarithm I wanted to write. I knew about `Nat.log` too, but I
didn't want that exactly either. My own implementation had a few of my own false
starts (which I could have avoided with pen and paper), but eventually I figured
out the **right** search terms. I was trawling through the files related to
`zpow` and realized that there was an `Int.log` with a definition essentially
identical to mine. After experiencing this, I realized that my usual go-to of
googling is a terrible way to learn a theory in Lean. Instead,

+ Try searching in mathlib documentation. You may need to scroll a lot.
+ Try searching for a theorem name with `exact?`.
+ Try searching with [leansearch.net](https://leansearch.net) or with `#leansearch`.
Despite being AI, the hype for leansearch is real. There's also Moogle, but I
never use it.
+ Search for theorems you might think are related to your
function.
+ Try searching zulip manually. Zulip is not typically indexed by Google.

Once I found the right theory for integer logarithms and powers, the remaining
theorems were easy enough. I learned much just by reading definitions
and associated proofs in those files. I was really cooking now.

Ultimately, it seems impossible to keep the names of all of the theorems
necessary for even ordinary algebra in my own memory.  Unless the lemmas and
theorems magically become more expressive, tactics become more powerful, or
something like that, it seems like something like leansearch is the future +
`exact?` of course. I wouldn't discount future magical changes in Lean though.

## Real-world tactics

There's also a variety of tactics that you'll see used in `mathlib` that I did
not use when learning from beginner guides. For example, Mathematics in
Lean doesn't tell you about `refine`, and `refine` shows up all the time
in actual code since it shortens proofs significantly. There are some other features
the beginner documentation tells you about, like substituting with `rfl` in calls to
`rcases` or other tactics. Unfortunately, this never worked out for me because `rfl`
doesn't rewrite beyond single variables. Similarly, tactics like
`apply_fun`, which is a tactic that should apply a function to both sides of an
equation, was extremely flaky and I couldn't get it to work in a single real
proof.

Later, I systematically went through all the tactics available in
`Mathlib.Tactics` and figured out what they actually did. Out of this,
I discovered many tactics which were indispensable.

## Positivity

For instance, `positivity` is indispensable. `positivity` is a tactic that
proves whether a quantity is positive. That actually covers non-negative,
non-zero, or just positive. I thought, this is the bee's knees when I found
it, and I was right.

Since a lot of theorems in `mathlib` generally, and specifically floating point
numbers, involve proving that certain quantities, positive or non-negative or
non-zero, so you can divide and cancel things, you use it a lot for basic
algebra.  When you write your own functions or more complicated expressions, you
can also extend the tactic in a way that `positivity` will apply to it. This is
very important because it can save you time in way more cases, even when you
aren't calling `positivity` yourself.

```lean demo
#print evalRoundNearInt  -- my own extension of positivity
```

```
open Lean Meta Qq Mathlib.Meta.Positivity in
@[positivity round_near_int _]
def evalRoundNearInt : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℤ), ~q(round_near_int $a) =>
    let zα : Q(Zero ℚ) := q(inferInstance)
    let pα : Q(PartialOrder ℚ) := q(inferInstance)
    assumeInstancesCommute
    match ← core zα pα a with
    | .positive pa => pure (.nonnegative q(round_near_int_of_pos $pa))
    | .nonnegative pa => pure (.nonnegative q(round_near_int_of_nonneg $pa))
    | _ => pure .none
```

That said, you seem to only be able to extend `positivity` calls for function
calls and not general pattern matching like `simp`. Often times, I identified
key expressions that needed to be positive, such as part of the mantissa `|q| / 2^Int.log |q| - 1`,
but I ended up using a lemma instead, which was less
convenient. I am not sure how users are even supposed to find strange positivity
lemmas like this anyways merely by search. Here is a little theorem
I used a lot for the size of the mantissa, which couldn't be eliminated with automation:

```lean demo
example (q : ℚ) (h : q ≠ 0): 1 ≤ |q| * (2 ^ Int.log 2 |q|)⁻¹ ∧
  |q| * (2 ^ Int.log 2 |q|)⁻¹ < 2 := by  -- A key theorem about mantissa sizes
  constructor
  · suffices (2 ^ Int.log 2 |q|) ≤ |q| by
      rw [<-mul_one (2 ^ _)] at this
      rw [mul_comm]
      exact (le_inv_mul_iff₀ (zpow_pos rfl _ : (0 : ℚ) < 2 ^ Int.log 2 |q|)).2 this
    exact Int.zpow_log_le_self (by norm_num) (abs_pos.mpr h)
  suffices |q| < 2 ^ (Int.log 2 |q| + 1) by
    rw [zpow_add_one₀ (by norm_num), mul_comm] at this
    exact (mul_inv_lt_iff₀ (zpow_pos rfl _ : (0 : ℚ) < 2 ^ Int.log 2 |q|)).2 this
  apply Int.lt_zpow_succ_log_self (by norm_num : 1 < 2)
```

If I had to redo everything, I would actually factor more complicated
expressions into functions that I can then prove positivity constraints about.
In a similar vein, `gcongr` looks like another excellent tactic here, which
I did not fully grok.

## Simplifier and Normalization Tactics

Mathematics in Lean taught me tactics such as `group`, `ring`, `field_simp`,
but I found them to not be very effective. They were intended to finish proofs
and not really simplify proofs. Even `field_simp` often went in
unexpected directions, especially when powers got involved.

Most of my time algebra bashing was spent figuring out how to either get to a
place where a group or ring could do its job, or to figure out how to do the
last manipulation so that `field_simp` would actually do something useful.

Some tactics I discovered later were a lot more helpful than I thought at first.
The `simp?` tactic is a great way to make partial progress in a predictable way.
The other tactic I found to be helpful in a very late stage was `omega`, which
lets you prove general facts about integers. Since most of what I was doing
involved rational numbers, it wasn't as effective, which is a little bit
surprising because I would expect that rational numbers and integers to be
extremely similar.

On the normalization side, `norm_cast`, `qify`, and `zify` helped heaps
since there is a lot of casting between natural numbers, integers, and
rationals. I learned about these when I tried to prove that $`\sqrt{2}` is
irrational as in  $`\neg \exists q \in \mathbb{Q}, q^2 = 2`. Just doing that was
quite an exercise since it is not straightforward how to do anything with
coercion or with rationals in Lean.

## Tactics I didn't figure out how to use

One lingering reflection has been how my understanding of some tactics
remains tantalizingly limited.

1. `aesop`: As a general solver, it can probably do a lot more, but the
configuration seemed challenging, and I didn't know how to get started. It doesn't
seem useful by default.

2. Custom `simp` lemmas: It's unclear what should
be a simp lemma and when you should just pass your lemma to simp with `simp
[your_lemma]`, so that's usually what I did instead.

3. [`bound`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Bound.html):
which seems like it should do almost exactly what I want a lot, but I never
actually found a specific scenario in which it worked. This may be user error.

## "Without Loss of Generality" tactic

I have avoided discussing the `wlog` tactic, since I have mixed feelings about
recommending it as a go-to option. In some theorems, it lets you clear out
specific cases very quickly, but it often hides the higher order logic that
binds all your theorems in similar structures. `wlog` lets you assert a
statement and prove that if the theorem is true while asserting the statement,
then it is true when negating the statement. However, this often obscures some
symmetry arguments that are useful to extract out as their own lemmas or
pseudo-induction theorems.

Earlier I listed out several examples of special cases. Many times I tried using
`wlog` and had to refactor later. For dealing with a positive and negative
case, I started out by using `wlog`, but it's cleaner to define `neg` functions
on the representations and a set of theorems there. Similarly, I created a
theorem to apply symmetry arguments on the rationals to prove theorems of the
type `P q1 q2`.

Special cases in general seems to have no silver bullet.

## Splitting tactics I'm unsure about

`split_ifs`, `split`, `match`, and `if` can all be used to split theorems into
special cases either defined by users or defined by the goal of a proof instead.
I have no idea which one is the "best" to use at any given time. They all seem
to have their own gotchas in terms of manual work and labeling hypotheses.

Sometimes I also discovered that default way to split a function
_definition_ is counterproductive to how you want to split the _theorem_ into pieces.
As discussed earlier, `splitIsFinite` defined a better way to split floats
into pieces than I could get with any standard tactic.

## General proof structure

As a more positive note, I learned much about how to structure routine proofs
without symmetry / higher-order methods. There's a lot more use of `apply`,
`have`, and `suffices` than I thought. I would say 90% of the effort is writing
out which of those three and their corresponding term. Sometimes, the statement
trivially matches what I would write in $`\LaTeX`, but other times, a proof
requires a bit of finagling with `suffices`. I'm not disappointed at all with
the experience; it was mainly a matter of practice to become proficient.

## Named Arguments

Beyond the more Lean-specific programming patterns, I also learned the value of
the Lean 4 language features. As a new feature in Lean 4, named arguments are
criminally underutilized.  The standard library hasn't caught up on informative
names, and in fact, the documentation is pretty light on its usage too. I found
named arguments to be one of the most helpful features, and I will deeply miss it in any
functional programming language from now on.

When you define a lemma in Lean, you typically make any variables that can be
inferred from later theorems as implicit with `{q : Rat}`. However, this does
not help you when you are applying _backwards reasoning_. The standard approach
in the documentation is to specify what you are missing with `@lemma_name _ _ _ q`
or however many `_` you need for the other inferred variables. With named
arguments, you can do `lemma_name (q := q)`.

The only downside is that too many theorems do not have meaningful names for
hypotheses. If there is only one hypothesis, then it's `h`, otherwise ¯\\\_(ツ)\_/¯.
Informative arguments do not seem to really be a priority yet.

## Things I didn't learn but expected to (AKA Future Directions)

As a few counter-examples to the neat programming techniques I've learned,
I didn't learn some fundamentals I was hoping to:

- What's the best way to write readable Lean code?
	- Should I be using `show` more?
	- I definitely should be using more comments.
- How do you make your library easy to use, easy to understand, and extensible?
- Should I be using type class inference or implicit variables?
	I went back and forth on this very often, and currently think I should have
	gone with type classes for floating point parameters like precision or maximum
	exponent.

	If I'd known about named arguments for type classes, it would have changed my
	decision as well. I recall having problems with specifying the parameters in
	an inductive theorem, but that was probably a skill issue.

Overall, I believe I will slowly gain experience on this if I contribute
to mathlib more directly, or through later experimental projects. Hence,
I do not want to stick around on endlessly refactoring `Flean` for
readability before I know what that means.

## Things I knew but didn't want to believe

Since I am somewhat stubborn and hopeful, I seemed to refuse to take some
advice I saw before I even started: You should write your theorems out on paper first,
and you will be forced into more generality eventually. Everything is more complicated
than you expect. Approaching a theorem from scratch, it felt very difficult to get a
lot of traction on it because everything felt obvious. As I went on, I discovered
the most important factors of a proof, and I'd have to refactor my system to work
in more general settings just so I can get new rounding modes. I'd have to think
about what are the elements that are most important, the things that would let me
use `mathlib` to the greatest effect. I wanted to believe that `mathlib`'s size
would make any choice of proof equally simple, which was wrong.

## Things I should have learned but didn't

As a counterexample to my ability to learn, some fundamentals still haven't
"clicked":

- I still don't feel very solid about mathlib's naming scheme
- I have no idea how to generate documentation, and I didn't write any.
- I don't know the correct way to namespace things. I suspect I need a lot more namespaces.

# {label conclusion}[Concluding Thoughts about Lean in General]

There's this little aphorism I occasionally repeat to myself: to solve your
problem, first solve first order logic. I feel like that applies to `Flean` too. The
existing tactics and language features in Lean still feel vaguely incomplete.
There feels like a lot of low-hanging fruit, maybe on the software engineering side
of defining tactics.

Consider some "bad" yet astounding tactics. `apply?` doesn't return useful
searches even with the `using` keyword, but still searches through many theorems.
Similarly, `conv?` often fails when the expressions become too complicated to
select, but should let you click around in the goal. A la Tantalus, it seems it's not
easy to pick low-hanging fruit.

Some features of tactics lift my spirits as new tools for mathematics. They
- return partial progress like `simp`
- let you inspect and modify search like `simp?`
- let you cache search and see small proof outputs also like `simp?`.
- are extensible like `positivity`.
- play nicely with other tactics like `gcongr`.

Ultimately, I expect tactics to rarely "solve" everything (excepting AGI).
For every tool, there is a problem it cannot solve. Not every tool needs to
completely decide a problem, so it's important to return partial progress
and allow users to pick up where tools leave off, expanding the set of decidable
problems.
