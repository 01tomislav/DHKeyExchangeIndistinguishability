# A feasibility probe: UC-style security proofs in Lean 4

The question this repository was built to answer is narrow and practical:

> Can the basic constructs of Universal Composability, and the parts of a UC
> proof that actually cost effort, be carried out in Lean 4 at all?

If they cannot, there is no point in building a full framework. If they can,
there is. **They can** — this repository contains a complete, machine-checked,
`sorry`-free proof of an indistinguishability statement about a Diffie–Hellman
key exchange, together with all the infrastructure it needed.

What follows is what was proved, what was deliberately left out, what went
wrong along the way, and what the next step would cost.

---

## 1. Result

`Indist.lean` is 3,389 lines. It compiles in about 9 seconds on top of a cached
Mathlib, contains no `sorry`, and the top-level theorem depends on exactly one
domain assumption:

```
#print axioms experimentIdeal_experimentReal
  ⟹  [propext, pwr_comm, Classical.choice, Quot.sound]
```

`propext`, `Classical.choice` and `Quot.sound` are Lean's standard axioms.
`pwr_comm` is the single cryptographic assumption: that exponentiation
commutes, `(g^x)^y = (g^y)^x`.

Nothing else is assumed. 

## 2. The statement

```lean
theorem experimentIdeal_experimentReal :
  ∀ (outBit : Bool) (env : SPin),
  experimentIdeal outBit env - experimentReal outBit env ≤ least_upper_bound
```

Reading it:

- `env` is an arbitrary environment: any state type, any probabilistic
  transition function. It is not restricted to be efficient.
- `experimentReal outBit env` is the probability that `env`, interacting with
  the real protocol, ends the run with output bit `outBit`.
  `experimentIdeal` is the same measurement against the ideal protocol.
- `least_upper_bound` is the smallest `ε` such that *no* test whatsoever can
  separate the real key distribution from the ideal one with advantage above
  `ε`. Since the tests range over all Boolean functions, this is exactly the
  statistical (total variation) distance between the two distributions.

The bound is the same expression for `outBit = true` and `outBit = false`, and
it does not mention `env`. So: **no environment can tell the real protocol from
the ideal one any better than the underlying key distributions can be told
apart.** That is a reduction, and it is the shape a UC emulation proof takes.

A second, sharper form is also proved, and it is the one that would survive a
later restriction to efficient distinguishers:

```lean
theorem advantage_preserving (outBit : Bool) (env : SPin) :
    experimentIdeal outBit env - experimentReal outBit env
      ≤ (∑' t, distroI t * G outBit env t.1 t.2.1 t.2.2)
        - (∑' t, distroR t * G outBit env t.1 t.2.1 t.2.2)
```

Here `G outBit env` is a concrete distinguisher built from `env` itself — the
environment replayed against a hard-wired transcript. This step loses nothing.
The step from here to `least_upper_bound` is where information is thrown away,
and it is exactly the step that a computational version of this development
would replace.

## 3. The two protocols

The real protocol is textbook Diffie–Hellman over channels that the adversary
can observe and block but not modify (an authenticated-channel, `F_AUTH`-style
assumption, realised here by the `Forwarder` machine):

```
pt1 draws q1, sends g^q1 to pt2 through fwd1
fwd1 shows the message to env, waits for env's go-ahead, then delivers it
pt2 draws q2, computes ke = (g^q1)^q2 and reports it to env
env prompts pt2, which sends g^q2 to pt1 through fwd2
fwd2 shows, waits, delivers
pt1 computes ke = (g^q2)^q1 and reports it to env
```

The two computed keys agree by `pwr_comm`. This is the only place the
assumption is used.

The ideal protocol is an ideal key-exchange functionality (`KEIdeal`, an
`F_KE`-style box that hands both parties the same fresh key `g^q3`) together
with a concrete simulator (`KESim`, which manufactures the transcript `g^q1`,
`g^q2` from its own randomness), plus dummy parties and dummy adversary
interfaces so that the environment sees the same four pin names in both worlds:

```
REAL                                 IDEAL
  pt1 ── fwd1 ── pt2                   pt1 ── keideal ── pt2
  pt2 ── fwd2 ── pt1                   keideal ── kesim
  env ── pt1, pt2, fwd1, fwd2          kesim ── fwd1, fwd2
                                       env ── pt1, pt2, fwd1, fwd2
```

The two key distributions the proof reduces to are the DDH tuples:

```
distroR = (g^q1, g^q2, (g^q2)^q1)        distroI = (g^r1, g^r2, g^r3)
```

## 4. The model

Since we are not reproducing the UC computational model literally, here is the
exact correspondence.

| UC | here |
|---|---|
| interactive Turing machine with tapes | `Machine α`: a state plus `String → Message → α → PMF (Message × α)` — a transition that returns a *distribution* over (reply, new state) instead of consuming a random tape |
| control function restricting external writes | `Router.wires`: an explicit list of unordered pairs of pin names |
| identity / PID | `Pin.name : String` |
| adversary `A` | folded into the environment: in the real world `env` is wired directly to the forwarders, i.e. the dummy adversary |
| simulator `S` | `KESim`, given concretely |
| ideal functionality `F` | `KEIdeal` |
| `Z` outputs a bit | `env` ends the run by sending a message to `"experiment"` whose content is `"1"` or `"0"`; any other content counts as no output |

The last row deserves a note. `Message.content` is a `String`, so a message that
ought to carry a bit can carry anything; the experiment's outcome type is
therefore `Option Bool` rather than `Bool`. That partiality is an artefact of
keeping `Message` monomorphic, not a feature of the model.

## 5. What is *not* here

Stated plainly, because a reviewer will ask:

- **No composition theorem.** This is the single largest gap and the point of the proposed continuation.
- **No efficiency bounds.** The environment is unrestricted, which is why the bound must be statistical. As a *security* claim about Diffie–Hellman the theorem is therefore empty until DDH and a feasibility restriction are added; what is proved is the reduction, not the hardness.
- **No group structure.** `pwr` is opaque with `pwr_comm` as its only property, so nothing forces `distroR`/`distroI` to be a real DDH instance.
- **No multiple sessions or session identifiers.** Pins are addressed by a flat
  `String`, so two instances of the same protocol cannot currently coexist.
- **No corruption of parties.**
- **No quantification over adversaries.** The dummy adversary is built into the
  design rather than justified by the usual dummy-adversary theorem.


## 6. Three obstacles, and where each one stands

These are the things that made this look risky before it was tried.

**Reasoning about probability at scale — solved.** The whole development is
`PMF`/`ENNReal`, with suprema over step bounds, `tsum` manipulation and
commuting sums past suprema. About 2,700 of the 3,389 lines are proof, and none
of it needed new probability theory beyond Mathlib.

**Serialising messages inside messages — solved.** Protocol machines pack a
message into the content of another message. Lean 4.32's string API is
`ByteArray`-backed with slices and iterators and has no `List Char`
characterisation of `takeWhile`, so `Message.fromString (toString m) = m` had to
be built from scratch. It is now a theorem for arbitrary content, not an axiom
and not a `native_decide` on fixed strings.

**Universe levels when protocols nest — real, measured, and avoidable.** The
obvious way to compose protocols is to let a sub-protocol be a machine whose
state is a router. With a universe-polymorphic `Machine`, `Machine Router.{0}`
is well-typed and lives in `Type 1` — but it then packs into `SPin.{1}`, i.e.
into `Router.{1}`, not back into `Router.{0}`:

```
Application type mismatch: The argument
  Router
has type
  Type 1
of sort `Type 2` but is expected to have type
  Type
of sort `Type 1` in the application
  PSigma.mk Router
```

Nesting raises the level each time, so there is no fixed point, and universe
polymorphism alone does not fix it.

The way out is not to nest types at all. Composition should flatten: given a
protocol and a sub-protocol, produce a single flat router in which the
sub-protocol's pins are renamed by prefixing, so that an identity becomes a
*path* rather than a name. `Router` then stays in `Type 1` and composition is an
ordinary function `Router → Router → Router`. The same prefixing doubles as the
session-identifier mechanism needed for multiple instances. This is the approach
taken in EasyUC, where identities are lists of integers ("addresses") and a full
address is obtained by prefixing.

Concretely, hierarchical identities can be carried in the existing
`Pin.name : String` without changing any type, because this repository already
contains a proved injective encoding of structured data into a string together
with its decoder — the self-delimiting round-trip above. That lemma was not
incidental; it is the enabling ingredient for addressing under composition.

## 7. Proposed next step

A bounded spike, cheap enough to buy before committing to anything:

1. define `Router.compose` by prefixing pin names and wires;
2. prove that routing in `ρ.compose "sub" π` on a prefixed name agrees with
   routing in `π`;
3. prove that the composed experiment produces the same transcript.

If those go through, the universe risk is retired and the remainder of a
composition theorem is work rather than research. If they do not, that is known
in days instead of months. Beyond the spike, a composition theorem also needs a
notion of protocol-with-a-hole, session identifiers, and either the
dummy-adversary theorem or explicit quantification over adversaries.

## 8. Prior work

The closest existing effort is **EasyUC** (Canetti, Stoughton and Varia, CSF
2019), which mechanises UC in EasyCrypt which heavily influenced this work and from which the address-prefixing idea above is taken.

Reference for the model itself: R. Canetti, *Universally Composable Security*,
Journal of the ACM 67(5), 2020.

## 9. Effort

A week of part-time human work, plus a few hours and about
US$120 of AI agent time, for 3,389 lines of Lean of which roughly 2,700 are
proof. The proof was written by an AI agent (Claude) under light human
direction; the definitions, the modelling decisions and the statement of the
theorem are the author's.

## 10. Building

```
lake exe cache get      # fetch Mathlib binaries
lake build              # ~9 s for Indist.lean on top of a cached Mathlib
```

Toolchain: `leanprover/lean4:v4.32.1`, Mathlib `v4.32.0-rc1`. Continuous
integration is configured in `.github/workflows/lean_action_ci.yml`.

To check the axiom footprint yourself:

```lean
import Indist
#print axioms experimentIdeal_experimentReal
```
