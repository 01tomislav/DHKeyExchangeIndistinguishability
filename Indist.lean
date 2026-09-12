import  Mathlib.Data.Finset.Basic
import  Mathlib.Data.Finset.Card
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Countable.Defs
import Mathlib.Logic.Encodable.Basic

/------------------------------------------------------------------------------
We setup a simplified infrastructure needed to describe
the execution and messaging between Interactive Turing Machines (ITMs)
of Universal Composability as Lean constructs.
------------------------------------------------------------------------------/

/-
The `Message` structure is used for communication between machines in the protocol.
The `destination_name` field specifies the intended recipient of the message,
while the `content` field contains the message content.
-/
structure Message where
  (destination_name : String)
  (content : String)
  deriving DecidableEq, Repr, Inhabited, Hashable

/-
The `string2selfdelimitingString` function converts a string into
a self-delimiting string by prepending its length.
We'll be using this function to encode a message as the content of another message.
-/
def string2selfdelimitingString : String -> String :=
  fun s => toString s.length ++ ":" ++ s

/-
The `selfdelimitingString2string` function decodes a self-delimiting string
back into the original string and the remaining content.
We'll be using this function to decode the content of a message
back into the original message.
-/
def selfdelimitingString2string : String -> String × String:=
  fun s =>
    let len := s.takeWhile Char.isDigit
    let lenlen := len.positions.length
    let lenInt := len.toNat!
    let rest := String.Slice.copy (s.drop (lenlen +1))
    let str := rest.take (lenInt)
    (String.Slice.copy str, String.Slice.copy (rest.drop (lenInt)))

/-
The `ToString` allows us to convert
a message into a string representation.
-/
instance : ToString Message where
  toString m :=  (string2selfdelimitingString m.destination_name) ++ m.content

/-
The `fromString` allows us to convert
a string representation back into a message.
-/
def Message.fromString (s : String) : Message :=
  let (dest, rest) := selfdelimitingString2string s
  { destination_name := dest, content := rest }

/-
In case a machine receives a message with an invalid content,
or from an unexpected sender,
it will return an error message back to the sender.
-/
def contentError := "error"

noncomputable def Machine.errorMessage2sender {α : Type} (sender : String) (s : α) : PMF (Message × α) :=
  PMF.pure ({ destination_name := sender, content := contentError }, s)

/-
The `Machine` structure represents a machine in the protocol,
with a state and a probabilistic function for processing messages.
The function `func` takes a sender name, a message, and the current state,
and returns a probability mass function (PMF) over pairs of new messages and new states.
-/
structure Machine (α : Type) where
  state : α
  func : String -> Message -> α -> PMF (Message × α)

/-
The `Pin` structure represents a communication endpoint in the protocol.
An instance of a machine has a single pin in the protocol,
which is used to send and receive messages.
The `name` field serves as the identity of the machine in the protocol,
and the `machine` field contains the actual machine instance.
\alpha is the type of the state of the machine.
-/
structure Pin (α : Type) where
  (name : String)
  (machine : Machine α)

/-
The `Pin.invoke` function invokes
the processing function of its associated machine.
The return value is a PMF over pair of
the returned message and the new state of the machine.
-/
noncomputable def Pin.invoke {α : Type} (s : String) (p : Pin α) (m : Message) : PMF (Message × Pin α) :=
  do
  let (newMessage, newState) ← p.machine.func s m p.machine.state
  PMF.pure (newMessage, { name := p.name, machine := { state := newState, func := p.machine.func } })

/-
The `Wire` structure represents a connection between two pins in the protocol.
Two pins can communicate with each other if they are connected by a wire.
-/
structure Wire where
  w :  Finset String
  twoDistinctPins : w.card = 2

/-
The `SPin` type is a dependent pair of a type and a pin of that type.
We use this type to store a list of pins of different types
representing machines in the protocol.
-/
def SPin : Type 1 := PSigma fun (α : Type) => Pin α

/-
The `Router` structure represents the pins (machines with their identities) of the protocol
and their "communication sets" represented as wires.
-/
structure Router where
  (pins : List SPin)
  (wires : List Wire)

/-
Helper function to replace a pin in a list with a new pin based on its name.
-/
def changePinOfName
(lista : List SPin) (name : String)
(newPin : SPin) : List SPin :=
  lista.map fun ⟨α, p⟩ =>
    if p.name == name then
      newPin
    else
      ⟨α, p⟩

/-
The `startMessage` is the initial message sent to the environment
to start the protocol execution.
-/
noncomputable def startMessage : Message :=
  { destination_name := "env",
    content := "start" }

/-
The `destinationEnvMessage` is a function that takes a message and returns
a message with the destination set to "env",
and the content set to the string representation of the original message.
-/
noncomputable def destinationEnvMessage : Message → Message :=
  fun m => { destination_name := "env", content := toString m }

/-
The helper function`convertrsm` converts a router, string, and message PMF
into a PMF over a tuple of the router, string, and message.
-/
noncomputable def convertrsm (r : Router) (s : String) (m : PMF Message)
    : PMF (Router × String × Message) :=
  PMF.bind m (fun msg => PMF.pure (r, s, msg))

/-
The `route` function takes a router, a source pin name, and a message,
and invokes the appropriate machine based on the message's destination.
The invoked machine may return a new message and a new state,
which are then used to update the router and the source pin name and the next message
for the next step in the protocol.
In case there is no wire connecting the source and destination pins,
or the destination pin is not found in the router,
the router will return a message with the destination set to "env"
and the content set to the string representation of the original message.

The special cases:
When the message's destination is "experiment",
the router returns the current state and message without invoking any machine,
as this indicates that the protocol has reached its end and the result is returned to the experiment.

When the source name is "experiment" and the message's destination is "env",
as the experiment is not a machine, and is not part of the protocol,
a dummy wire is created to allow the message to be sent to the environment.
-/
noncomputable def Router.route : Router -> String -> Message
-> PMF (Router × String × Message)
  | r, p, m =>
    if m.destination_name = "experiment"
    then PMF.pure (r, p, m)
    else
      let wire :=
      if (p = "experiment" && m.destination_name = "env")
      then
        some {w := {"experiment", "env"}, twoDistinctPins := by decide}
      else
        r.wires.find? (fun w =>
        p ∈ w.w && m.destination_name ∈ w.w)
      match wire with
      | some _ =>
        let destpin := r.pins.find? (fun p => p.snd.name = m.destination_name)
        match destpin with
        | some apin =>
          PMF.bind (Pin.invoke p apin.snd m) (fun (newMessage, newPin) =>
          let newPins := changePinOfName r.pins apin.snd.name ⟨apin.fst, newPin⟩
          let newRouter : Router := { pins := newPins, wires := r.wires }
          PMF.pure (newRouter, apin.snd.name, newMessage))
        | none =>
          PMF.pure (r, p, destinationEnvMessage m)
      | none =>
        PMF.pure (r, p, destinationEnvMessage m)

/-
The `ReturnsToExperiment_within_n_steps` function computes the probability
that a message will be sent to the "experiment" within `n` steps of routing.
-/
noncomputable def ReturnsToExperiment_within_n_steps : Router -> String -> Message -> Nat
-> PMF Bool
| _, _, m, 0 =>
    if m.destination_name = "experiment"
    then PMF.pure true
    else PMF.pure false
| r, s, m, (n+1) =>
   if m.destination_name = "experiment"
   then PMF.pure true
   else
     let nextStep := Router.route r s m
     PMF.bind nextStep (fun (r', s', m') =>
       ReturnsToExperiment_within_n_steps r' s' m' n)

/-
The `ReturnsToExperiment` function computes the probability
that a message will eventually be sent to the "experiment".
-/
noncomputable def ReturnsToExperiment : Router → String -> Message → ENNReal
| r, s, m =>
  ⨆ (k : Nat), (ReturnsToExperiment_within_n_steps r s m k) true

/-
The `StartExperiment` function starts the experiment by sending the `startMessage`
to the environment through the router, and computes the probability
that the message will eventually be returned to the "experiment".
-/
noncomputable def StartExperiment : Router -> ENNReal :=
  fun r => ReturnsToExperiment r "experiment" startMessage

/-----------------------------------------------------------------------
As an example of using the above infrastructure,
we'll define the real and ideal versions of the Diffie-Hellman key exchange protocol,
and prove that if there is some environment that can distinguish the two
with some probability, then there is a distinguisher that can distinguish
the distributions of the keys generated by the two protocols with the same probability.
-----------------------------------------------------------------------/

/-
We will be drawing exponents from an opaque distribution `rnd` over the natural numbers,
which will be used to generate the keys in the Diffie-Hellman protocol.
-/
noncomputable opaque rnd : PMF Nat

/-
The power function `pwr` is defined as an opaque function,
and its commutativity property is stated as an axiom.
For simplicity, we don't use a group structure here,
but rather just strings and natural numbers.
We use strings for base and the result,
since we use strings as message contents.
-/
opaque pwr : String → Nat → String
axiom pwr_comm : ∀ (g : String) (x y : Nat), pwr (pwr g x) y = pwr (pwr g y) x

/-
The `Forwarder` machine forwards one message from one machine to another machine,
with an intermediate step, where it sends the message to the environment,
and then waits for an "OK" message from the environment to send the original message
to the destination machine. This models a communication channel where an adversary
can see the message and can choose to block it but not modify it.
-/
inductive ForwarderState where
  | Init : ForwarderState
  | WaitOK (m : Message) : ForwarderState
  | Done : ForwarderState

noncomputable def Forwarder : Machine ForwarderState where
  state := ForwarderState.Init
  func := fun sender (m:Message) s =>
    match s with
    | ForwarderState.Init =>
      if sender ≠ "env" then
        let content := string2selfdelimitingString sender ++ m.content
        let newMessage : Message :=
        { destination_name := "env", content := content }
        PMF.pure (newMessage, ForwarderState.WaitOK (Message.fromString m.content))
      else
        Machine.errorMessage2sender sender s
    | ForwarderState.WaitOK m' =>
        if sender = "env" then
          PMF.pure (m', ForwarderState.Done)
        else
          Machine.errorMessage2sender sender s
    | ForwarderState.Done =>
      Machine.errorMessage2sender sender s

/-
The `Pt1` and `Pt2` machines implement the two parties in the
Diffie-Hellman key exchange protocol.
-/
inductive Pt1State where
  | WaitReq1 : Pt1State
  | WaitFwd2 (q : Nat) : Pt1State
  | Done : Pt1State

noncomputable def Pt1 : Machine Pt1State where
  state := Pt1State.WaitReq1
  func := fun sender (m :Message) s =>
    match s with
    | Pt1State.WaitReq1 => do
      let q1 ← rnd
      let k1 := pwr "g" q1
      let newMessage : Message :=
      { destination_name := "pt2", content := k1 }
      let fwdMessage : Message :=
      { destination_name := "fwd1", content := toString newMessage }
      PMF.pure (fwdMessage, Pt1State.WaitFwd2 q1)
    | Pt1State.WaitFwd2 q1 =>
      if sender = "fwd2" then
        let k2 := m.content
        let ke := pwr k2 q1
        let newMessage : Message :=
        /-  -/
        { destination_name := "env", content := ke }
        PMF.pure (newMessage, Pt1State.Done)
      else
        Machine.errorMessage2sender sender s
    | Pt1State.Done =>
      Machine.errorMessage2sender sender s

inductive Pt2State where
  | WaitFwd1 : Pt2State
  | WaitReq2 (q2 : Nat) : Pt2State
  | Done : Pt2State

noncomputable def Pt2 : Machine Pt2State where
  state := Pt2State.WaitFwd1
  func := fun sender (m:Message) s =>
    match s with
    | Pt2State.WaitFwd1 =>
      if sender = "fwd1" then
        let k1 := m.content
        do
        let q2 ← rnd
        let ke := pwr k1 q2
        let newMessage : Message :=
        {destination_name := "env", content := ke }
        PMF.pure (newMessage, Pt2State.WaitReq2 q2)
      else
        Machine.errorMessage2sender sender s
    | Pt2State.WaitReq2 q2 =>
      if sender = "env" then
        let k2 := pwr "g" q2
        let newMessage : Message :=
        { destination_name := "pt1", content := k2 }
        let fwdMessage : Message :=
        { destination_name := "fwd2", content := toString newMessage }
        PMF.pure (fwdMessage, Pt2State.Done)
      else
        Machine.errorMessage2sender sender s
    | Pt2State.Done =>
      Machine.errorMessage2sender sender s

/-
The experimentReal function sets up the real Diffie-Hellman key exchange protocol,
and returns the probability that the protocol will eventually
return a message to the "experiment".
We don't look at the content of the message returned to the experiment,
we interpret the return of the message as the decision of the environment
that it was interacting with (say) the real protocol.
-/
noncomputable def Pt1Pin : Pin Pt1State := { name := "pt1", machine := Pt1 }
noncomputable def Pt2Pin : Pin Pt2State := { name := "pt2", machine := Pt2 }
noncomputable def Fwd1Pin : Pin ForwarderState := { name := "fwd1", machine := Forwarder }
noncomputable def Fwd2Pin : Pin ForwarderState := { name := "fwd2", machine := Forwarder }
noncomputable def experimentReal (env : SPin) : ENNReal :=
    let router : Router :=
    { pins := [
      ⟨Pt1State, Pt1Pin⟩,
      ⟨Pt2State, Pt2Pin⟩,
      ⟨ForwarderState, Fwd1Pin⟩,
      ⟨ForwarderState, Fwd2Pin⟩,
      env],
      wires := [
        { w := { "pt1", "fwd1" }, twoDistinctPins := by decide },
        { w := { "pt2", "fwd2" }, twoDistinctPins := by decide },
        { w := { "pt1", "env" }, twoDistinctPins := by decide },
        { w := { "pt2", "env" }, twoDistinctPins := by decide },
        { w := { "fwd1", "env" }, twoDistinctPins := by decide },
        { w := { "fwd2", "env" }, twoDistinctPins := by decide },
        { w := { "fwd1", "pt2" }, twoDistinctPins := by decide },
        { w := { "fwd2", "pt1" }, twoDistinctPins := by decide }
      ] }
    StartExperiment router

/-
The `KEIdeal` together with the `KESim` machine implements
the ideal Diffie-Hellman key exchange protocol.
We introduce dummy machines for the two parties, and the two forwarders,
so the pins that the environment can communicate with are the same as in the real protocol.
-/
inductive KEIdealState where
  | WaitReq1 : KEIdealState
  | WaitSim1 : KEIdealState
  | WaitReq2 (q : Nat) : KEIdealState
  | WaitSim2 (q : Nat) : KEIdealState
  | Done : KEIdealState

noncomputable def KEIdeal : Machine KEIdealState where
  state := KEIdealState.WaitReq1
  func := fun sender (_ : Message) s =>
    match s with
    | KEIdealState.WaitReq1 =>
      if sender = "pt1" then
        let newMessage : Message :=
        { destination_name := "kesim", content := "" }
        PMF.pure (newMessage, KEIdealState.WaitSim1)
      else
        Machine.errorMessage2sender sender s
    | KEIdealState.WaitSim1 =>
      if sender = "kesim" then
        do
        let q3 ← rnd
        let ke := pwr "g" q3
        let newMessage : Message :=
        { destination_name := "pt2", content := ke }
        PMF.pure (newMessage, KEIdealState.WaitReq2 q3)
      else
        Machine.errorMessage2sender sender s
    | KEIdealState.WaitReq2 q =>
      if sender = "pt2"
      then
        let newMessage : Message :=
        { destination_name := "kesim", content := "" }
        PMF.pure (newMessage, KEIdealState.WaitSim2 q)
      else
        Machine.errorMessage2sender sender s
    | KEIdealState.WaitSim2 q =>
      if sender = "kesim" then
        let ke := pwr "g" q
        let newMessage : Message := { destination_name := "pt1", content := ke }
        PMF.pure (newMessage, KEIdealState.Done)
      else
        Machine.errorMessage2sender sender s
    | KEIdealState.Done =>
      Machine.errorMessage2sender sender s

inductive KESimState where
  | WaitReq1 : KESimState
  | WaitAdv1 : KESimState
  | WaitReq2 (q2 : Nat) : KESimState
  | WaitAdv2 : KESimState
  | Done : KESimState

noncomputable def KESim : Machine KESimState where
  state := KESimState.WaitReq1
  func := fun sender (_ : Message) s =>
    match s with
    | KESimState.WaitReq1 =>
      if sender = "keideal" then
        do
        let q1 <- rnd
        let k1 := pwr "g" q1
        let newMessage : Message :=
        { destination_name := "pt2", content := k1 }
        let content := string2selfdelimitingString "pt1" ++ toString newMessage
        let fwdMessage : Message :=
        { destination_name := "fwd1", content := content }
        PMF.pure (fwdMessage, KESimState.WaitAdv1)
      else
        Machine.errorMessage2sender sender s
    | KESimState.WaitAdv1 =>
      if sender = "fwd1" then
        do
        let q2 <- rnd
        let newMessage : Message :=
        { destination_name := "keideal", content := "" }
        PMF.pure (newMessage, KESimState.WaitReq2 q2)
      else
        Machine.errorMessage2sender sender s
    | KESimState.WaitReq2 q2 =>
      if sender = "keideal" then
        let k2 := pwr "g" q2
        let newMessage : Message :=
        { destination_name := "pt1", content := k2 }
        let content := string2selfdelimitingString "pt2" ++ toString newMessage
        let fwdMessage : Message :=
        { destination_name := "fwd2", content := content }
        PMF.pure (fwdMessage, KESimState.WaitAdv2)
      else
        Machine.errorMessage2sender sender s
    | KESimState.WaitAdv2 =>
      if sender = "fwd2" then
        let newMessage : Message :=
        { destination_name := "keideal", content := "" }
        PMF.pure (newMessage, KESimState.Done)
      else
          Machine.errorMessage2sender sender s
    | KESimState.Done =>
      Machine.errorMessage2sender sender s

noncomputable def DummyPt : Machine Unit where
  state := ()
  func := fun sender (m:Message) s =>
    if sender = "env" then
      let content := toString m
      let newMessage : Message :=
      { destination_name := "keideal", content := content }
      PMF.pure (newMessage, s)
    else
      let newMessage : Message :=
      { destination_name := "env", content := m.content }
      PMF.pure (newMessage, s)

noncomputable def DummyAdv : Machine Unit where
  state := ()
  func := fun sender (m:Message) s =>
    if sender = "env" then
      let content := string2selfdelimitingString sender ++ toString m
      let newMessage : Message :=
      { destination_name := "kesim", content := content }
      PMF.pure (newMessage, s)
    else
      let newMessage : Message :=
      { destination_name := "env", content := m.content }
      PMF.pure (newMessage, s)

/-
The experimentIdeal function sets up the ideal Diffie-Hellman key exchange protocol,
and returns the probability that the protocol will eventually
return a message to the "experiment".
-/
noncomputable def IdealPin : Pin KEIdealState := { name := "keideal", machine := KEIdeal }
noncomputable def SimPin : Pin KESimState := { name := "kesim", machine := KESim }
noncomputable def DummyPt1Pin : Pin Unit := { name := "pt1", machine := DummyPt }
noncomputable def DummyPt2Pin : Pin Unit := { name := "pt2", machine := DummyPt }
noncomputable def DummyFwd1Pin : Pin Unit := { name := "fwd1", machine := DummyAdv }
noncomputable def DummyFwd2Pin : Pin Unit := { name := "fwd2", machine := DummyAdv }
noncomputable def experimentIdeal (env : SPin) : ENNReal :=
    let router : Router :=
    { pins := [
      ⟨KEIdealState, IdealPin⟩,
      ⟨KESimState, SimPin⟩,
      ⟨Unit, DummyPt1Pin⟩,
      ⟨Unit, DummyPt2Pin⟩,
      ⟨Unit, DummyFwd1Pin⟩,
      ⟨Unit, DummyFwd2Pin⟩,
      env],
      wires := [
        { w := { "keideal", "kesim" }, twoDistinctPins := by decide },
        { w := { "pt1", "keideal" }, twoDistinctPins := by decide },
        { w := { "pt2", "keideal" }, twoDistinctPins := by decide },
        { w := { "pt1", "env" }, twoDistinctPins := by decide },
        { w := { "pt2", "env" }, twoDistinctPins := by decide },
        { w := { "kesim", "fwd1" }, twoDistinctPins := by decide },
        { w := { "kesim", "fwd2" }, twoDistinctPins := by decide },
        { w := { "fwd1", "env" }, twoDistinctPins := by decide },
        { w := { "fwd2", "env" }, twoDistinctPins := by decide }
      ] }
    StartExperiment router

/-
The `distroR` function defines the distribution of random variables for the
real Diffie-Hellman key exchange protocol.
-/
noncomputable def distroR :=
  do
  let q1 ← rnd
  let q2 ← rnd
  let k1 := pwr "g" q1
  let k2 := pwr "g" q2
  let ke := pwr k2 q1
  PMF.pure (k1,k2,ke)

/-
The `distroI` function defines the distribution of random variables for the
ideal Diffie-Hellman key exchange protocol.
-/
noncomputable def distroI :=
  do
  let r1 ← rnd
  let r2 ← rnd
  let r3 ← rnd
  let i1 := pwr "g" r1
  let i2 := pwr "g" r2
  let i3 := pwr "g" r3
  PMF.pure (i1,i2,i3)

/-
The `dist_probR` function computes the probability that a given function
evaluates to true for the keys from distroR distribution.
-/
noncomputable def dist_probR (func : String × String × String → Bool) : PMF Bool :=
  PMF.bind distroR (fun (k1,k2,ke) =>
  PMF.pure (func (k1,k2,ke)))

/-
The `dist_probI` function computes the probability that a given function
evaluates to true for the keys from distroI distribution.
-/
noncomputable def dist_probI (func : String × String × String → Bool) : PMF Bool :=
  PMF.bind distroI (fun (i1,i2,i3) =>
  PMF.pure (func (i1,i2,i3)))

/-
The `dist_prob` function returns the difference between the probabilities
of a given function evaluating to true for the keys
from distroR and distroI distributions.
-/
noncomputable def dist_prob (func : String × String × String → Bool) : ENNReal :=
  let probR := (dist_probR func) true
  let probI := (dist_probI func) true
  probR - probI

/-
eps is an upper bound if for all functions func,
the dist_prob of func is less than eps.
-/
def upper_bound (eps : ENNReal) : Prop :=
  ∀ (func : String × String × String → Bool),
  dist_prob func ≤ eps

/-
The least_upper_bound function is the smallest number for which upper_bound holds.
-/
noncomputable def least_upper_bound : ENNReal :=
  sInf {x : ENNReal | upper_bound x}


/-
We can now state the main theorem of the Diffie-Hellman key exchange protocol,
which says that if there is an environment that can distinguish the real and ideal
protocols with some probability, then there is a distinguisher that can distinguish
the distributions of the keys generated by the two protocols with the same probability.

theorem experimentIdeal_experimentReal :
  ∀ (env : SPin),
  experimentIdeal env - experimentReal env ≤ least_upper_bound

The proof of this theorem is below, written by Claude AI agent, with minimal input from user.
-/

-- ===========================================================================
-- Round-trip theorem (self-delimiting decode∘encode).  The content here is
-- `pwr "g" q` with `q` a bound random variable, so it has to be proved for
-- arbitrary strings rather than discharged by `native_decide`.
-- ===========================================================================

section Roundtrip

/-- If `L` splits as `A ++ B` with every element of `A` satisfying `p` and the first
element of `B` (if any) failing `p`, then `A` is exactly `L.takeWhile p`. -/
private theorem list_takeWhile_of_split {α} {p : α → Bool} :
    ∀ (A B L : List α), A ++ B = L → (∀ a ∈ A, p a) → (∀ b, B.head? = some b → ¬ p b) →
      L.takeWhile p = A := by
  intro A
  induction A with
  | nil =>
    intro B L h _ hB
    subst h
    cases B with
    | nil => simp
    | cons b bs =>
      simp only [List.nil_append, List.takeWhile_cons]
      have : ¬ p b := hB b rfl
      simp [this]
  | cons a as ih =>
    intro B L h ha hB
    subst h
    have hpa : p a := ha a (by simp)
    simp only [List.cons_append, List.takeWhile_cons, hpa, if_true]
    congr 1
    exact ih B (as ++ B) rfl (fun x hx => ha x (by simp [hx])) hB

/-- `String.Slice.takeWhile` computes `List.takeWhile` on the underlying character list. -/
private theorem slice_toList_takeWhile (p : Char → Bool) (s : String.Slice) :
    (s.takeWhile p).copy.toList = s.copy.toList.takeWhile p := by
  have happ : (s.takeWhile p).copy ++ (s.dropWhile p).copy = s.copy :=
    String.Slice.takeWhile_append_dropWhile
  have hall : ∀ a ∈ (s.takeWhile p).copy.toList, p a := by
    have h := String.Slice.all_takeWhile (pat := p) (s := s)
    rw [String.Slice.all_bool_eq] at h
    simpa [List.all_eq_true] using h
  have hstart : (s.dropWhile p).startsWith p = false := by
    have h := String.Slice.isEmpty_takeWhile_dropWhile (pat := p) (s := s)
    rw [String.Slice.isEmpty_takeWhile, Bool.not_eq_true'] at h
    exact h
  rw [String.Slice.startsWith_bool_eq_head?] at hstart
  refine (list_takeWhile_of_split (s.takeWhile p).copy.toList (s.dropWhile p).copy.toList
    s.copy.toList ?_ hall ?_).symm
  · rw [← String.toList_append, happ]
  · intro b hb
    rw [hb] at hstart
    simp at hstart
    simp [hstart]

private theorem string_toList_takeWhile (p : Char → Bool) (s : String) :
    (s.takeWhile p).copy.toList = s.toList.takeWhile p := by
  rw [String.takeWhile, slice_toList_takeWhile, String.copy_toSlice]

/-- The position iterator of a slice yields one position per character. -/
private theorem slice_positions_length (s : String.Slice) :
    s.positions.length = s.copy.toList.length := by
  rw [← Std.Iter.length_toList_eq_length, String.Slice.toList_positions,
    ← String.Slice.Model.map_get_positionsFrom_startPos (s := s), List.length_map]

/-- The state machine inside `String.Slice.isNat` never rejects a list of digits. -/
private theorem isNat_aux : ∀ (L : List Char) (b : Bool), (∀ c ∈ L, c.isDigit = true) →
    (forIn L (((none : Option Bool), b)) (fun c (st : Option Bool × Bool) =>
        (if c = '_' then
              (if (!st.2) = true then pure (ForInStep.done (some false, st.2))
              else pure (ForInStep.yield (none, false)))
            else
              (if c.isDigit = true then pure (ForInStep.yield (none, true))
              else pure (ForInStep.done (some false, st.2))) : Id _)))
      = ((none : Option Bool), if L = [] then b else true) := by
  intro L
  induction L with
  | nil => intro b _; rfl
  | cons c L ih =>
    intro b h
    have hc : c.isDigit = true := h c (by simp)
    have hc' : ¬ (c = '_') := by rintro rfl; exact absurd hc (by decide)
    rw [List.forIn_cons]
    simp only [hc, hc', if_false, if_true]
    exact (ih true (fun x hx => h x (List.mem_cons_of_mem _ hx))).trans (by simp)

private theorem slice_isNat_of_digits (s : String.Slice) (hne : s.copy.toList ≠ [])
    (hd : ∀ c ∈ s.copy.toList, c.isDigit = true) : s.isNat = true := by
  rw [String.Slice.isNat]
  simp only [Id.run, String.Slice.forIn_eq_forIn_toList, isNat_aux _ _ hd, hne, if_false]
  rfl

private theorem list_foldl_eq_ofDigitChars :
    ∀ (L : List Char) (init : Nat), (∀ c ∈ L, c.isDigit = true) →
      L.foldl (fun n c => if c = '_' then n else n * 10 + (c.toNat - '0'.toNat)) init
        = Nat.ofDigitChars 10 L init := by
  intro L
  induction L with
  | nil => intro init _; simp
  | cons c L ih =>
    intro init h
    have hc : c.isDigit = true := h c (by simp)
    have hc' : ¬ (c = '_') := by rintro rfl; exact absurd hc (by decide)
    rw [List.foldl_cons, Nat.ofDigitChars_cons, ih _ (fun x hx => h x (List.mem_cons_of_mem _ hx)),
      if_neg hc', Nat.mul_comm init 10]

private theorem slice_toNat!_of_digits (s : String.Slice) (hne : s.copy.toList ≠ [])
    (hd : ∀ c ∈ s.copy.toList, c.isDigit = true) :
    s.toNat! = Nat.ofDigitChars 10 s.copy.toList 0 := by
  rw [String.Slice.toNat!, if_pos (slice_isNat_of_digits s hne hd),
    String.Slice.foldl_eq_foldl_toList, list_foldl_eq_ofDigitChars _ _ hd]

/-- Decoding the self-delimiting encoding of `d` followed by arbitrary trailing
data `c` recovers `d` and `c`. -/
theorem selfdelimitingString2string_string2selfdelimitingString (d c : String) :
    selfdelimitingString2string (string2selfdelimitingString d ++ c) = (d, c) := by
  set s : String := string2selfdelimitingString d ++ c with hs
  set N : String := toString d.length with hN
  -- the character list of the encoded string
  have hNdig : ∀ x ∈ N.toList, x.isDigit = true := by
    intro x hx
    rw [hN] at hx
    exact Nat.isDigit_of_mem_toDigits (b := 10) (n := d.length) (by decide) (by decide)
      (by simpa using hx)
  have hNne : N.toList ≠ [] := by simp [hN]
  have hsl : s.toList = N.toList ++ (':' :: (d.toList ++ c.toList)) := by
    simp [hs, string2selfdelimitingString, string2selfdelimitingString, ← hN, String.toList_append,
      show (":" : String).toList = [':'] from rfl]
  -- step 1: `takeWhile Char.isDigit` recovers the length prefix
  have hlen : (s.takeWhile Char.isDigit).copy.toList = N.toList := by
    rw [string_toList_takeWhile, hsl]
    refine list_takeWhile_of_split N.toList (':' :: (d.toList ++ c.toList)) _ rfl hNdig ?_
    intro b hb
    simp only [List.head?_cons, Option.some.injEq] at hb
    subst hb
    decide
  -- step 2: the number of positions is the length of the prefix
  have hlenlen : (s.takeWhile Char.isDigit).positions.length = N.toList.length := by
    rw [slice_positions_length, hlen]
  -- step 3: the prefix decodes back to `d.length`
  have hlenInt : (s.takeWhile Char.isDigit).toNat! = d.length := by
    rw [slice_toNat!_of_digits _ (by rw [hlen]; exact hNne) (by rw [hlen]; exact hNdig), hlen]
    simp [hN]
  -- step 4: dropping the prefix and the separator leaves `d ++ c`
  have hrest : (String.Slice.copy (s.drop (N.toList.length + 1))).toList = d.toList ++ c.toList := by
    rw [String.toList_copy_drop, hsl]
    simp [List.drop_append]
  simp only [selfdelimitingString2string, hlenlen, hlenInt]
  refine Prod.ext ?_ ?_
  · rw [← String.toList_inj, String.toList_copy_take, hrest,
      show d.length = d.toList.length from String.length_toList.symm]
    simp
  · rw [← String.toList_inj, String.toList_copy_drop, hrest,
      show d.length = d.toList.length from String.length_toList.symm]
    simp

end Roundtrip

theorem message_roundtrip (m : Message) : Message.fromString (toString m) = m := by
  show Message.fromString (string2selfdelimitingString m.destination_name ++ m.content) = m
  rw [Message.fromString, selfdelimitingString2string_string2selfdelimitingString]

-- ===========================================================================
-- Generic facts about cfgReturns / ReturnsToExperiment  (machine independent,
-- ported from the deterministic-content development in Indistinguishability/)
-- ===========================================================================

noncomputable def cfgReturns (r : Router) (s : String) (m : Message) (k : ℕ) : ENNReal :=
  (ReturnsToExperiment_within_n_steps r s m k) true

theorem cfgReturns_def (r s m) (k : ℕ) :
    cfgReturns r s m k = (ReturnsToExperiment_within_n_steps r s m k) true := rfl

theorem ReturnsToExperiment_eq_iSup (r s m) :
    ReturnsToExperiment r s m = ⨆ k, cfgReturns r s m k := rfl

theorem cfgReturns_exp (r s m) (h : m.destination_name = "experiment") (k : ℕ) :
    cfgReturns r s m k = 1 := by
  cases k with
  | zero => simp [cfgReturns, ReturnsToExperiment_within_n_steps, h, PMF.pure_apply]
  | succ n => simp [cfgReturns, ReturnsToExperiment_within_n_steps, h, PMF.pure_apply]

theorem cfgReturns_zero_nexp (r s m) (h : m.destination_name ≠ "experiment") :
    cfgReturns r s m 0 = 0 := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, h, PMF.pure_apply]

theorem cfgReturns_succ_nexp {r s m} (h : m.destination_name ≠ "experiment") (n : ℕ) :
    cfgReturns r s m (n+1)
    = ((Router.route r s m).bind
        (fun (c : Router × String × Message) =>
          ReturnsToExperiment_within_n_steps c.1 c.2.1 c.2.2 n)) true := by
  simp only [cfgReturns, ReturnsToExperiment_within_n_steps, h, if_false]

theorem cfgReturns_pure_step {r s m r' s' m'} (h : m.destination_name ≠ "experiment")
    (hr : Router.route r s m = PMF.pure (r', s', m')) (n : ℕ) :
    cfgReturns r s m (n+1) = cfgReturns r' s' m' n := by
  rw [cfgReturns_succ_nexp h, hr, PMF.pure_bind]
  rfl

theorem cfgReturns_succ_bind {r s m} (h : m.destination_name ≠ "experiment") (n : ℕ) :
    cfgReturns r s m (n+1)
    = ∑' c : Router × String × Message, (Router.route r s m) c * cfgReturns c.1 c.2.1 c.2.2 n := by
  rw [cfgReturns_succ_nexp h, PMF.bind_apply]
  rfl

theorem cfgReturns_env_deliver {r s m r2} {D : PMF Message} (h : m.destination_name ≠ "experiment")
    (hr : Router.route r s m = D.bind (fun msg => PMF.pure (r2, "env", msg))) (n : ℕ) :
    cfgReturns r s m (n+1) = ∑' msg : Message, D msg * cfgReturns r2 "env" msg n := by
  rw [cfgReturns_succ_nexp h, hr, PMF.bind_bind]
  simp only [PMF.pure_bind]
  rw [PMF.bind_apply]
  rfl

theorem cfgReturns_mono : ∀ (k : ℕ) (r : Router) (s : String) (m : Message),
    cfgReturns r s m k ≤ cfgReturns r s m (k+1) := by
  intro k
  induction k with
  | zero =>
    intro r s m
    by_cases h : m.destination_name = "experiment"
    · rw [cfgReturns_exp r s m h, cfgReturns_exp r s m h]
    · rw [cfgReturns_zero_nexp r s m h]; exact zero_le'
  | succ n ih =>
    intro r s m
    by_cases h : m.destination_name = "experiment"
    · rw [cfgReturns_exp r s m h, cfgReturns_exp r s m h]
    · rw [cfgReturns_succ_bind h, cfgReturns_succ_bind h]
      apply ENNReal.tsum_le_tsum
      intro c
      exact mul_le_mul_left' (ih c.1 c.2.1 c.2.2) _

theorem cfgReturns_monotone (r s m) : Monotone (fun k => cfgReturns r s m k) :=
  monotone_nat_of_le_succ (fun k => cfgReturns_mono k r s m)

theorem cfgReturns_le_add (r s m) (k a : ℕ) :
    cfgReturns r s m k ≤ cfgReturns r s m (k + a) :=
  cfgReturns_monotone r s m (Nat.le_add_right k a)

theorem iSup_cfgReturns_shift (r s m) (a : ℕ) :
    (⨆ k, cfgReturns r s m (k + a)) = ⨆ k, cfgReturns r s m k := by
  apply le_antisymm
  · exact iSup_le (fun k => le_iSup (fun j => cfgReturns r s m j) (k + a))
  · exact iSup_le (fun k => le_trans (cfgReturns_le_add r s m k a) (le_iSup (fun j => cfgReturns r s m (j + a)) k))

theorem ReturnsToExperiment_pure_step {r s m r' s' m'} (h : m.destination_name ≠ "experiment")
    (hr : Router.route r s m = PMF.pure (r', s', m')) :
    ReturnsToExperiment r s m = ReturnsToExperiment r' s' m' := by
  rw [ReturnsToExperiment_eq_iSup, ReturnsToExperiment_eq_iSup]
  apply le_antisymm
  · apply iSup_le; intro k
    cases k with
    | zero => rw [cfgReturns_zero_nexp r s m h]; exact zero_le'
    | succ n => rw [cfgReturns_pure_step h hr]; exact le_iSup (fun j => cfgReturns r' s' m' j) n
  · apply iSup_le; intro k
    rw [← cfgReturns_pure_step h hr]
    exact le_iSup (fun j => cfgReturns r s m j) (k+1)

theorem ReturnsToExperiment_of_peel {r s m r' s' m'} (a : ℕ)
    (hpeel : ∀ n, cfgReturns r s m (n + a) = cfgReturns r' s' m' n) :
    ReturnsToExperiment r s m = ReturnsToExperiment r' s' m' := by
  rw [ReturnsToExperiment_eq_iSup r' s' m', ReturnsToExperiment_eq_iSup r s m,
     ← iSup_cfgReturns_shift r s m a]
  apply iSup_congr
  intro k
  exact hpeel k

-- Swap of ⨆ and ∑' for monotone families (monotone convergence)

theorem finsetSum_iSup_comm {β : Type*} (s : Finset β) (g : ℕ → β → ENNReal)
    (hg : ∀ b, Monotone (fun k => g k b)) :
    ∑ b ∈ s, (⨆ k, g k b) = ⨆ k, ∑ b ∈ s, g k b := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, ih, ENNReal.iSup_add_iSup_of_monotone (hg a)
        (fun i j hij => Finset.sum_le_sum (fun b _ => hg b hij))]
    apply iSup_congr
    intro k
    rw [Finset.sum_insert ha]

theorem tsum_iSup_comm {β : Type*} (g : ℕ → β → ENNReal)
    (hg : ∀ b, Monotone (fun k => g k b)) :
    ∑' b, (⨆ k, g k b) = ⨆ k, ∑' b, g k b := by
  apply le_antisymm
  · rw [ENNReal.tsum_eq_iSup_sum]
    apply iSup_le
    intro s
    rw [finsetSum_iSup_comm s g hg]
    apply iSup_le
    intro k
    exact le_iSup_of_le k (ENNReal.sum_le_tsum s)
  · apply iSup_le
    intro k
    apply ENNReal.tsum_le_tsum
    intro b
    exact le_iSup (fun j => g j b) k

theorem tsum_mul_iSup_comm {β : Type*} (D : β → ENNReal) (f : ℕ → β → ENNReal)
    (hf : ∀ b, Monotone (fun k => f k b)) :
    ∑' b, D b * (⨆ k, f k b) = ⨆ k, ∑' b, D b * f k b := by
  have hmul : (fun b => D b * ⨆ k, f k b) = fun b => ⨆ k, D b * f k b := by
    funext b; exact ENNReal.mul_iSup _ _
  rw [hmul]
  exact tsum_iSup_comm (fun k b => D b * f k b) (fun b i j hij => mul_le_mul_left' (hf b hij) _)

-- ===========================================================================
-- Replay (deterministic-content, ideal-shaped) protocol, parameterized by the
-- three key strings.  Its acceptance probability `G` is the common continuation
-- that both experiments decompose over.
-- ===========================================================================

noncomputable def KEIdealR (ke : String) : Machine KEIdealState where
  state := KEIdealState.WaitReq1
  func := fun sender (_ : Message) s =>
    match s with
    | KEIdealState.WaitReq1 =>
      if sender = "pt1" then
        PMF.pure ({ destination_name := "kesim", content := "" }, KEIdealState.WaitSim1)
      else Machine.errorMessage2sender sender s
    | KEIdealState.WaitSim1 =>
      if sender = "kesim" then
        PMF.pure ({ destination_name := "pt2", content := ke }, KEIdealState.WaitReq2 0)
      else Machine.errorMessage2sender sender s
    | KEIdealState.WaitReq2 q =>
      if sender = "pt2" then
        PMF.pure ({ destination_name := "kesim", content := "" }, KEIdealState.WaitSim2 q)
      else Machine.errorMessage2sender sender s
    | KEIdealState.WaitSim2 _ =>
      if sender = "kesim" then
        PMF.pure ({ destination_name := "pt1", content := ke }, KEIdealState.Done)
      else Machine.errorMessage2sender sender s
    | KEIdealState.Done => Machine.errorMessage2sender sender s

noncomputable def KESimR (k1 k2 : String) : Machine KESimState where
  state := KESimState.WaitReq1
  func := fun sender (_ : Message) s =>
    match s with
    | KESimState.WaitReq1 =>
      if sender = "keideal" then
        let newMessage : Message := { destination_name := "pt2", content := k1 }
        let content := string2selfdelimitingString "pt1" ++ toString newMessage
        PMF.pure ({ destination_name := "fwd1", content := content }, KESimState.WaitAdv1)
      else Machine.errorMessage2sender sender s
    | KESimState.WaitAdv1 =>
      if sender = "fwd1" then
        PMF.pure ({ destination_name := "keideal", content := "" }, KESimState.WaitReq2 0)
      else Machine.errorMessage2sender sender s
    | KESimState.WaitReq2 _ =>
      if sender = "keideal" then
        let newMessage : Message := { destination_name := "pt1", content := k2 }
        let content := string2selfdelimitingString "pt2" ++ toString newMessage
        PMF.pure ({ destination_name := "fwd2", content := content }, KESimState.WaitAdv2)
      else Machine.errorMessage2sender sender s
    | KESimState.WaitAdv2 =>
      if sender = "fwd2" then
        PMF.pure ({ destination_name := "keideal", content := "" }, KESimState.Done)
      else Machine.errorMessage2sender sender s
    | KESimState.Done => Machine.errorMessage2sender sender s

def idealWires : List Wire :=
  [ { w := { "keideal", "kesim" }, twoDistinctPins := by decide },
    { w := { "pt1", "keideal" }, twoDistinctPins := by decide },
    { w := { "pt2", "keideal" }, twoDistinctPins := by decide },
    { w := { "pt1", "env" }, twoDistinctPins := by decide },
    { w := { "pt2", "env" }, twoDistinctPins := by decide },
    { w := { "kesim", "fwd1" }, twoDistinctPins := by decide },
    { w := { "kesim", "fwd2" }, twoDistinctPins := by decide },
    { w := { "fwd1", "env" }, twoDistinctPins := by decide },
    { w := { "fwd2", "env" }, twoDistinctPins := by decide } ]

noncomputable def replayPins (ke k1 k2 : String) (env : SPin) : List SPin :=
  [ ⟨KEIdealState, { name := "keideal", machine := KEIdealR ke }⟩,
    ⟨KESimState, { name := "kesim", machine := KESimR k1 k2 }⟩,
    ⟨Unit, DummyPt1Pin⟩,
    ⟨Unit, DummyPt2Pin⟩,
    ⟨Unit, DummyFwd1Pin⟩,
    ⟨Unit, DummyFwd2Pin⟩,
    env ]

noncomputable def G (env : SPin) (k1 k2 ke : String) : ENNReal :=
  StartExperiment { pins := replayPins ke k1 k2 env, wires := idealWires }

-- ===========================================================================
-- Deterministic (hardwired) real-shaped machines, parameterized by the
-- exponents q1, q2 (which stay variables), and the deterministic real
-- experiment detReal.
-- ===========================================================================

noncomputable def Pt1F (q1 : Nat) : Machine Pt1State where
  state := Pt1State.WaitReq1
  func := fun sender (m : Message) s =>
    match s with
    | Pt1State.WaitReq1 =>
      let k1 := pwr "g" q1
      let newMessage : Message := { destination_name := "pt2", content := k1 }
      let fwdMessage : Message := { destination_name := "fwd1", content := toString newMessage }
      PMF.pure (fwdMessage, Pt1State.WaitFwd2 q1)
    | Pt1State.WaitFwd2 q1 =>
      if sender = "fwd2" then
        let k2 := m.content
        let ke := pwr k2 q1
        PMF.pure ({ destination_name := "env", content := ke }, Pt1State.Done)
      else Machine.errorMessage2sender sender s
    | Pt1State.Done => Machine.errorMessage2sender sender s

noncomputable def Pt2F (q2 : Nat) : Machine Pt2State where
  state := Pt2State.WaitFwd1
  func := fun sender (m : Message) s =>
    match s with
    | Pt2State.WaitFwd1 =>
      if sender = "fwd1" then
        let k1 := m.content
        let ke := pwr k1 q2
        PMF.pure ({ destination_name := "env", content := ke }, Pt2State.WaitReq2 q2)
      else Machine.errorMessage2sender sender s
    | Pt2State.WaitReq2 q2 =>
      if sender = "env" then
        let k2 := pwr "g" q2
        let newMessage : Message := { destination_name := "pt1", content := k2 }
        let fwdMessage : Message := { destination_name := "fwd2", content := toString newMessage }
        PMF.pure (fwdMessage, Pt2State.Done)
      else Machine.errorMessage2sender sender s
    | Pt2State.Done => Machine.errorMessage2sender sender s

def realWires : List Wire :=
  [ { w := { "pt1", "fwd1" }, twoDistinctPins := by decide },
    { w := { "pt2", "fwd2" }, twoDistinctPins := by decide },
    { w := { "pt1", "env" }, twoDistinctPins := by decide },
    { w := { "pt2", "env" }, twoDistinctPins := by decide },
    { w := { "fwd1", "env" }, twoDistinctPins := by decide },
    { w := { "fwd2", "env" }, twoDistinctPins := by decide },
    { w := { "fwd1", "pt2" }, twoDistinctPins := by decide },
    { w := { "fwd2", "pt1" }, twoDistinctPins := by decide } ]

noncomputable def realPinsF (q1 q2 : Nat) (env : SPin) : List SPin :=
  [ ⟨Pt1State, { name := "pt1", machine := Pt1F q1 }⟩,
    ⟨Pt2State, { name := "pt2", machine := Pt2F q2 }⟩,
    ⟨ForwarderState, { name := "fwd1", machine := Forwarder }⟩,
    ⟨ForwarderState, { name := "fwd2", machine := Forwarder }⟩,
    env ]

noncomputable def detReal (env : SPin) (q1 q2 : Nat) : ENNReal :=
  StartExperiment { pins := realPinsF q1 q2 env, wires := realWires }

-- ===========================================================================
-- Generalized env-delivery (distro env is jointly randomized: the continuation
-- router depends on the sampled env pin).
-- ===========================================================================

theorem cfgReturns_env_deliver_gen {r s m} {A : Type} (D : PMF A) (F : A → Router) (Msg : A → Message)
    (h : m.destination_name ≠ "experiment")
    (hr : Router.route r s m = D.bind (fun a => PMF.pure (F a, "env", Msg a))) (n : ℕ) :
    cfgReturns r s m (n+1) = ∑' a, D a * cfgReturns (F a) "env" (Msg a) n := by
  rw [cfgReturns_succ_nexp h, hr, PMF.bind_bind]
  simp only [PMF.pure_bind]
  rw [PMF.bind_apply]
  rfl

theorem ReturnsToExperiment_env_deliver_gen {r s m} {A : Type} (D : PMF A) (F : A → Router)
    (Msg : A → Message) (h : m.destination_name ≠ "experiment")
    (hr : Router.route r s m = D.bind (fun a => PMF.pure (F a, "env", Msg a))) :
    ReturnsToExperiment r s m = ∑' a, D a * ReturnsToExperiment (F a) "env" (Msg a) := by
  rw [ReturnsToExperiment_eq_iSup r s m, ← iSup_cfgReturns_shift r s m 1]
  have hstep : ∀ k, cfgReturns r s m (k + 1) = ∑' a, D a * cfgReturns (F a) "env" (Msg a) k :=
    fun k => cfgReturns_env_deliver_gen D F Msg h hr k
  simp_rw [hstep]
  have hrte : ∀ a, ReturnsToExperiment (F a) "env" (Msg a) = ⨆ k, cfgReturns (F a) "env" (Msg a) k :=
    fun a => ReturnsToExperiment_eq_iSup (F a) "env" (Msg a)
  simp_rw [hrte]
  rw [tsum_mul_iSup_comm D (fun k a => cfgReturns (F a) "env" (Msg a) k)
      (fun a => cfgReturns_monotone (F a) "env" (Msg a))]

-- ===========================================================================
-- Phase routers for the deterministic real (detReal) and replay/ideal (G)
-- experiments, mirroring the reference development.
-- ===========================================================================

def sOK (s : String) : Prop :=
  s = "experiment" ∨ s = "pt1" ∨ s = "pt2" ∨ s = "fwd1" ∨ s = "fwd2" ∨ s = "env"

theorem sOK_experiment : sOK "experiment" := Or.inl rfl
theorem sOK_pt1 : sOK "pt1" := Or.inr (Or.inl rfl)
theorem sOK_pt2 : sOK "pt2" := Or.inr (Or.inr (Or.inl rfl))
theorem sOK_fwd1 : sOK "fwd1" := Or.inr (Or.inr (Or.inr (Or.inl rfl)))
theorem sOK_fwd2 : sOK "fwd2" := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
theorem sOK_env : sOK "env" := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

noncomputable def realPinsFst (q1 q2 : Nat) (p1 : Pt1State) (p2 : Pt2State) (f1 f2 : ForwarderState)
    (env : SPin) : List SPin :=
  [ ⟨Pt1State, { name := "pt1", machine := { state := p1, func := (Pt1F q1).func } }⟩,
    ⟨Pt2State, { name := "pt2", machine := { state := p2, func := (Pt2F q2).func } }⟩,
    ⟨ForwarderState, { name := "fwd1", machine := { state := f1, func := Forwarder.func } }⟩,
    ⟨ForwarderState, { name := "fwd2", machine := { state := f2, func := Forwarder.func } }⟩,
    env ]

noncomputable def RRF (q1 q2 : Nat) (i : ℕ) (env : SPin) : Router :=
  { pins := match i with
    | 0 => realPinsFst q1 q2 Pt1State.WaitReq1 Pt2State.WaitFwd1 ForwarderState.Init ForwarderState.Init env
    | 1 => realPinsFst q1 q2 (Pt1State.WaitFwd2 q1) Pt2State.WaitFwd1
             (ForwarderState.WaitOK {destination_name:="pt2",content:=pwr "g" q1}) ForwarderState.Init env
    | 2 => realPinsFst q1 q2 (Pt1State.WaitFwd2 q1) (Pt2State.WaitReq2 q2) ForwarderState.Done ForwarderState.Init env
    | 3 => realPinsFst q1 q2 (Pt1State.WaitFwd2 q1) Pt2State.Done ForwarderState.Done
             (ForwarderState.WaitOK {destination_name:="pt1",content:=pwr "g" q2}) env
    | _ => realPinsFst q1 q2 Pt1State.Done Pt2State.Done ForwarderState.Done ForwarderState.Done env
    , wires := realWires }

noncomputable def idealPinsRst (k1 k2 ke : String) (kei : KEIdealState) (ks : KESimState)
    (env : SPin) : List SPin :=
  [ ⟨KEIdealState, { name := "keideal", machine := { state := kei, func := (KEIdealR ke).func } }⟩,
    ⟨KESimState, { name := "kesim", machine := { state := ks, func := (KESimR k1 k2).func } }⟩,
    ⟨Unit, DummyPt1Pin⟩,
    ⟨Unit, DummyPt2Pin⟩,
    ⟨Unit, DummyFwd1Pin⟩,
    ⟨Unit, DummyFwd2Pin⟩,
    env ]

noncomputable def RIF (k1 k2 ke : String) (i : ℕ) (env : SPin) : Router :=
  { pins := match i with
    | 0 => idealPinsRst k1 k2 ke KEIdealState.WaitReq1 KESimState.WaitReq1 env
    | 1 => idealPinsRst k1 k2 ke KEIdealState.WaitSim1 KESimState.WaitAdv1 env
    | 2 => idealPinsRst k1 k2 ke (KEIdealState.WaitReq2 0) (KESimState.WaitReq2 0) env
    | 3 => idealPinsRst k1 k2 ke (KEIdealState.WaitSim2 0) KESimState.WaitAdv2 env
    | _ => idealPinsRst k1 k2 ke KEIdealState.Done KESimState.Done env
    , wires := idealWires }

-- ===========================================================================
-- Env-delivery for the concrete routers.
-- ===========================================================================

/-- The new env pin after env processes a message (name preserved). -/
noncomputable def envStep {eα : Type} (ep : Pin eα) (ns : eα) : Pin eα :=
  { name := ep.name, machine := { state := ns, func := ep.machine.func } }

theorem delivReal_gen (q1 q2 : Nat) (p1 : Pt1State) (p2 : Pt2State) (f1 f2 : ForwarderState)
    (eα : Type) (ep : Pin eα) (s : String) (m : Message)
    (henv : ep.name = "env") (hm : m.destination_name = "env") (hs : sOK s) :
    Router.route {pins := realPinsFst q1 q2 p1 p2 f1 f2 ⟨eα,ep⟩, wires := realWires} s m
    = (ep.machine.func s m ep.machine.state).bind (fun x =>
        PMF.pure ({pins := realPinsFst q1 q2 p1 p2 f1 f2 ⟨eα, envStep ep x.2⟩, wires := realWires}, "env", x.1)) := by
  rcases hs with h|h|h|h|h|h <;> subst h <;>
    simp [realPinsFst, realWires, Router.route, Pin.invoke, envStep, changePinOfName,
      hm, henv, List.find?, List.map, Finset.mem_insert, Finset.mem_singleton, bind]

theorem delivReal (q1 q2 : Nat) (i : ℕ) (hi : i ≤ 4) (eα : Type) (ep : Pin eα) (s : String) (m : Message)
    (henv : ep.name = "env") (hm : m.destination_name = "env") (hs : sOK s) :
    Router.route (RRF q1 q2 i ⟨eα,ep⟩) s m
    = (ep.machine.func s m ep.machine.state).bind (fun x =>
        PMF.pure (RRF q1 q2 i ⟨eα, envStep ep x.2⟩, "env", x.1)) := by
  rcases i with _|_|_|_|_|i
  · exact delivReal_gen _ _ _ _ _ _ eα ep s m henv hm hs
  · exact delivReal_gen _ _ _ _ _ _ eα ep s m henv hm hs
  · exact delivReal_gen _ _ _ _ _ _ eα ep s m henv hm hs
  · exact delivReal_gen _ _ _ _ _ _ eα ep s m henv hm hs
  · exact delivReal_gen _ _ _ _ _ _ eα ep s m henv hm hs
  · omega

theorem delivIdeal_gen (k1 k2 ke : String) (kei : KEIdealState) (ks : KESimState)
    (eα : Type) (ep : Pin eα) (s : String) (m : Message)
    (henv : ep.name = "env") (hm : m.destination_name = "env") (hs : sOK s) :
    Router.route {pins := idealPinsRst k1 k2 ke kei ks ⟨eα,ep⟩, wires := idealWires} s m
    = (ep.machine.func s m ep.machine.state).bind (fun x =>
        PMF.pure ({pins := idealPinsRst k1 k2 ke kei ks ⟨eα, envStep ep x.2⟩, wires := idealWires}, "env", x.1)) := by
  rcases hs with h|h|h|h|h|h <;> subst h <;>
    simp [idealPinsRst, idealWires, Router.route, Pin.invoke, envStep, changePinOfName,
      DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin, hm, henv, List.find?, List.map,
      Finset.mem_insert, Finset.mem_singleton, bind]

theorem delivIdeal (k1 k2 ke : String) (i : ℕ) (hi : i ≤ 4) (eα : Type) (ep : Pin eα) (s : String)
    (m : Message) (henv : ep.name = "env") (hm : m.destination_name = "env") (hs : sOK s) :
    Router.route (RIF k1 k2 ke i ⟨eα,ep⟩) s m
    = (ep.machine.func s m ep.machine.state).bind (fun x =>
        PMF.pure (RIF k1 k2 ke i ⟨eα, envStep ep x.2⟩, "env", x.1)) := by
  rcases i with _|_|_|_|_|i
  · exact delivIdeal_gen _ _ _ _ _ eα ep s m henv hm hs
  · exact delivIdeal_gen _ _ _ _ _ eα ep s m henv hm hs
  · exact delivIdeal_gen _ _ _ _ _ eα ep s m henv hm hs
  · exact delivIdeal_gen _ _ _ _ _ eα ep s m henv hm hs
  · exact delivIdeal_gen _ _ _ _ _ eα ep s m henv hm hs
  · omega

theorem envStep_name {eα : Type} (ep : Pin eα) (ns : eα) (henv : ep.name = "env") :
    (envStep ep ns).name = "env" := by rw [envStep]; exact henv

-- ===========================================================================
-- Phase-advancing peel lemmas (real: uses message_roundtrip; ideal: pure).
-- ===========================================================================

theorem peelR_0_pt1 (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RRF q1 q2 0 ⟨eα,ep⟩) "env" ({destination_name := "pt1", content := c} : Message) (n+2)
    = cfgReturns (RRF q1 q2 1 ⟨eα,ep⟩) "fwd1"
        ({destination_name := "env",
          content := string2selfdelimitingString "pt1"
            ++ toString ({destination_name := "pt2", content := pwr "g" q1} : Message)} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RRF, realPinsFst, realWires, Router.route,
    Pt1F, Pt2F, Forwarder, Pin.invoke, changePinOfName, destinationEnvMessage,
    Machine.errorMessage2sender, List.find?, List.map, henv, message_roundtrip, bind, PMF.pure_bind]

theorem peelR_1_fwd1 (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RRF q1 q2 1 ⟨eα,ep⟩) "env" ({destination_name := "fwd1", content := c} : Message) (n+2)
    = cfgReturns (RRF q1 q2 2 ⟨eα,ep⟩) "pt2"
        ({destination_name := "env", content := pwr (pwr "g" q1) q2} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RRF, realPinsFst, realWires, Router.route,
    Pt1F, Pt2F, Forwarder, Pin.invoke, changePinOfName, destinationEnvMessage,
    Machine.errorMessage2sender, List.find?, List.map, henv, message_roundtrip, bind, PMF.pure_bind]

theorem peelR_2_pt2 (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RRF q1 q2 2 ⟨eα,ep⟩) "env" ({destination_name := "pt2", content := c} : Message) (n+2)
    = cfgReturns (RRF q1 q2 3 ⟨eα,ep⟩) "fwd2"
        ({destination_name := "env",
          content := string2selfdelimitingString "pt2"
            ++ toString ({destination_name := "pt1", content := pwr "g" q2} : Message)} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RRF, realPinsFst, realWires, Router.route,
    Pt1F, Pt2F, Forwarder, Pin.invoke, changePinOfName, destinationEnvMessage,
    Machine.errorMessage2sender, List.find?, List.map, henv, message_roundtrip, bind, PMF.pure_bind]

theorem peelR_3_fwd2 (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RRF q1 q2 3 ⟨eα,ep⟩) "env" ({destination_name := "fwd2", content := c} : Message) (n+2)
    = cfgReturns (RRF q1 q2 4 ⟨eα,ep⟩) "pt1"
        ({destination_name := "env", content := pwr (pwr "g" q2) q1} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RRF, realPinsFst, realWires, Router.route,
    Pt1F, Pt2F, Forwarder, Pin.invoke, changePinOfName, destinationEnvMessage,
    Machine.errorMessage2sender, List.find?, List.map, henv, message_roundtrip, bind, PMF.pure_bind]

theorem peelI_0_pt1 (k1 k2 ke : String) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RIF k1 k2 ke 0 ⟨eα,ep⟩) "env" ({destination_name := "pt1", content := c} : Message) (n+4)
    = cfgReturns (RIF k1 k2 ke 1 ⟨eα,ep⟩) "fwd1"
        ({destination_name := "env",
          content := string2selfdelimitingString "pt1"
            ++ toString ({destination_name := "pt2", content := k1} : Message)} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RIF, idealPinsRst, idealWires, Router.route,
    KEIdealR, KESimR, DummyPt, DummyAdv, DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin,
    Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender,
    List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelI_1_fwd1 (k1 k2 ke : String) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RIF k1 k2 ke 1 ⟨eα,ep⟩) "env" ({destination_name := "fwd1", content := c} : Message) (n+4)
    = cfgReturns (RIF k1 k2 ke 2 ⟨eα,ep⟩) "pt2"
        ({destination_name := "env", content := ke} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RIF, idealPinsRst, idealWires, Router.route,
    KEIdealR, KESimR, DummyPt, DummyAdv, DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin,
    Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender,
    List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelI_2_pt2 (k1 k2 ke : String) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RIF k1 k2 ke 2 ⟨eα,ep⟩) "env" ({destination_name := "pt2", content := c} : Message) (n+4)
    = cfgReturns (RIF k1 k2 ke 3 ⟨eα,ep⟩) "fwd2"
        ({destination_name := "env",
          content := string2selfdelimitingString "pt2"
            ++ toString ({destination_name := "pt1", content := k2} : Message)} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RIF, idealPinsRst, idealWires, Router.route,
    KEIdealR, KESimR, DummyPt, DummyAdv, DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin,
    Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender,
    List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelI_3_fwd2 (k1 k2 ke : String) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RIF k1 k2 ke 3 ⟨eα,ep⟩) "env" ({destination_name := "fwd2", content := c} : Message) (n+4)
    = cfgReturns (RIF k1 k2 ke 4 ⟨eα,ep⟩) "pt1"
        ({destination_name := "env", content := ke} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RIF, idealPinsRst, idealWires, Router.route,
    KEIdealR, KESimR, DummyPt, DummyAdv, DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin,
    Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender,
    List.find?, List.map, henv, bind, PMF.pure_bind]

-- ===========================================================================
-- Error peel lemmas (real: wrong destination errors in 1 step).
-- ===========================================================================

theorem peelR_0_pt2 (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RRF q1 q2 0 ⟨eα,ep⟩) "env" ({destination_name := "pt2", content := c} : Message) (n+1)
    = cfgReturns (RRF q1 q2 0 ⟨eα,ep⟩) "pt2" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RRF, realPinsFst, realWires, Router.route, Pt1F, Pt2F, Forwarder, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelR_0_fwd1 (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RRF q1 q2 0 ⟨eα,ep⟩) "env" ({destination_name := "fwd1", content := c} : Message) (n+1)
    = cfgReturns (RRF q1 q2 0 ⟨eα,ep⟩) "fwd1" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RRF, realPinsFst, realWires, Router.route, Pt1F, Pt2F, Forwarder, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelR_0_fwd2 (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RRF q1 q2 0 ⟨eα,ep⟩) "env" ({destination_name := "fwd2", content := c} : Message) (n+1)
    = cfgReturns (RRF q1 q2 0 ⟨eα,ep⟩) "fwd2" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RRF, realPinsFst, realWires, Router.route, Pt1F, Pt2F, Forwarder, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelR_1_pt1 (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RRF q1 q2 1 ⟨eα,ep⟩) "env" ({destination_name := "pt1", content := c} : Message) (n+1)
    = cfgReturns (RRF q1 q2 1 ⟨eα,ep⟩) "pt1" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RRF, realPinsFst, realWires, Router.route, Pt1F, Pt2F, Forwarder, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelR_1_pt2 (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RRF q1 q2 1 ⟨eα,ep⟩) "env" ({destination_name := "pt2", content := c} : Message) (n+1)
    = cfgReturns (RRF q1 q2 1 ⟨eα,ep⟩) "pt2" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RRF, realPinsFst, realWires, Router.route, Pt1F, Pt2F, Forwarder, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelR_1_fwd2 (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RRF q1 q2 1 ⟨eα,ep⟩) "env" ({destination_name := "fwd2", content := c} : Message) (n+1)
    = cfgReturns (RRF q1 q2 1 ⟨eα,ep⟩) "fwd2" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RRF, realPinsFst, realWires, Router.route, Pt1F, Pt2F, Forwarder, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelR_2_pt1 (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RRF q1 q2 2 ⟨eα,ep⟩) "env" ({destination_name := "pt1", content := c} : Message) (n+1)
    = cfgReturns (RRF q1 q2 2 ⟨eα,ep⟩) "pt1" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RRF, realPinsFst, realWires, Router.route, Pt1F, Pt2F, Forwarder, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelR_2_fwd1 (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RRF q1 q2 2 ⟨eα,ep⟩) "env" ({destination_name := "fwd1", content := c} : Message) (n+1)
    = cfgReturns (RRF q1 q2 2 ⟨eα,ep⟩) "fwd1" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RRF, realPinsFst, realWires, Router.route, Pt1F, Pt2F, Forwarder, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelR_2_fwd2 (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RRF q1 q2 2 ⟨eα,ep⟩) "env" ({destination_name := "fwd2", content := c} : Message) (n+1)
    = cfgReturns (RRF q1 q2 2 ⟨eα,ep⟩) "fwd2" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RRF, realPinsFst, realWires, Router.route, Pt1F, Pt2F, Forwarder, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelR_3_pt1 (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RRF q1 q2 3 ⟨eα,ep⟩) "env" ({destination_name := "pt1", content := c} : Message) (n+1)
    = cfgReturns (RRF q1 q2 3 ⟨eα,ep⟩) "pt1" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RRF, realPinsFst, realWires, Router.route, Pt1F, Pt2F, Forwarder, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelR_3_pt2 (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RRF q1 q2 3 ⟨eα,ep⟩) "env" ({destination_name := "pt2", content := c} : Message) (n+1)
    = cfgReturns (RRF q1 q2 3 ⟨eα,ep⟩) "pt2" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RRF, realPinsFst, realWires, Router.route, Pt1F, Pt2F, Forwarder, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelR_3_fwd1 (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RRF q1 q2 3 ⟨eα,ep⟩) "env" ({destination_name := "fwd1", content := c} : Message) (n+1)
    = cfgReturns (RRF q1 q2 3 ⟨eα,ep⟩) "fwd1" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RRF, realPinsFst, realWires, Router.route, Pt1F, Pt2F, Forwarder, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelR_4_pt1 (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RRF q1 q2 4 ⟨eα,ep⟩) "env" ({destination_name := "pt1", content := c} : Message) (n+1)
    = cfgReturns (RRF q1 q2 4 ⟨eα,ep⟩) "pt1" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RRF, realPinsFst, realWires, Router.route, Pt1F, Pt2F, Forwarder, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelR_4_pt2 (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RRF q1 q2 4 ⟨eα,ep⟩) "env" ({destination_name := "pt2", content := c} : Message) (n+1)
    = cfgReturns (RRF q1 q2 4 ⟨eα,ep⟩) "pt2" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RRF, realPinsFst, realWires, Router.route, Pt1F, Pt2F, Forwarder, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelR_4_fwd1 (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RRF q1 q2 4 ⟨eα,ep⟩) "env" ({destination_name := "fwd1", content := c} : Message) (n+1)
    = cfgReturns (RRF q1 q2 4 ⟨eα,ep⟩) "fwd1" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RRF, realPinsFst, realWires, Router.route, Pt1F, Pt2F, Forwarder, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelR_4_fwd2 (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RRF q1 q2 4 ⟨eα,ep⟩) "env" ({destination_name := "fwd2", content := c} : Message) (n+1)
    = cfgReturns (RRF q1 q2 4 ⟨eα,ep⟩) "fwd2" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RRF, realPinsFst, realWires, Router.route, Pt1F, Pt2F, Forwarder, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

-- ===========================================================================
-- Error peel lemmas (ideal: wrong destination stalls in 3 steps).
-- ===========================================================================
theorem peelI_0_pt2 (k1 k2 ke : String) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RIF k1 k2 ke 0 ⟨eα,ep⟩) "env" ({destination_name := "pt2", content := c} : Message) (n+3)
    = cfgReturns (RIF k1 k2 ke 0 ⟨eα,ep⟩) "pt2" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RIF, idealPinsRst, idealWires, Router.route, KEIdealR, KESimR, DummyPt, DummyAdv, DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin, Pin.invoke, changePinOfName, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelI_0_fwd1 (k1 k2 ke : String) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RIF k1 k2 ke 0 ⟨eα,ep⟩) "env" ({destination_name := "fwd1", content := c} : Message) (n+3)
    = cfgReturns (RIF k1 k2 ke 0 ⟨eα,ep⟩) "fwd1" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RIF, idealPinsRst, idealWires, Router.route, KEIdealR, KESimR, DummyPt, DummyAdv, DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin, Pin.invoke, changePinOfName, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelI_0_fwd2 (k1 k2 ke : String) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RIF k1 k2 ke 0 ⟨eα,ep⟩) "env" ({destination_name := "fwd2", content := c} : Message) (n+3)
    = cfgReturns (RIF k1 k2 ke 0 ⟨eα,ep⟩) "fwd2" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RIF, idealPinsRst, idealWires, Router.route, KEIdealR, KESimR, DummyPt, DummyAdv, DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin, Pin.invoke, changePinOfName, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelI_1_pt1 (k1 k2 ke : String) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RIF k1 k2 ke 1 ⟨eα,ep⟩) "env" ({destination_name := "pt1", content := c} : Message) (n+3)
    = cfgReturns (RIF k1 k2 ke 1 ⟨eα,ep⟩) "pt1" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RIF, idealPinsRst, idealWires, Router.route, KEIdealR, KESimR, DummyPt, DummyAdv, DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin, Pin.invoke, changePinOfName, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelI_1_pt2 (k1 k2 ke : String) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RIF k1 k2 ke 1 ⟨eα,ep⟩) "env" ({destination_name := "pt2", content := c} : Message) (n+3)
    = cfgReturns (RIF k1 k2 ke 1 ⟨eα,ep⟩) "pt2" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RIF, idealPinsRst, idealWires, Router.route, KEIdealR, KESimR, DummyPt, DummyAdv, DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin, Pin.invoke, changePinOfName, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelI_1_fwd2 (k1 k2 ke : String) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RIF k1 k2 ke 1 ⟨eα,ep⟩) "env" ({destination_name := "fwd2", content := c} : Message) (n+3)
    = cfgReturns (RIF k1 k2 ke 1 ⟨eα,ep⟩) "fwd2" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RIF, idealPinsRst, idealWires, Router.route, KEIdealR, KESimR, DummyPt, DummyAdv, DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin, Pin.invoke, changePinOfName, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelI_2_pt1 (k1 k2 ke : String) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RIF k1 k2 ke 2 ⟨eα,ep⟩) "env" ({destination_name := "pt1", content := c} : Message) (n+3)
    = cfgReturns (RIF k1 k2 ke 2 ⟨eα,ep⟩) "pt1" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RIF, idealPinsRst, idealWires, Router.route, KEIdealR, KESimR, DummyPt, DummyAdv, DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin, Pin.invoke, changePinOfName, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelI_2_fwd1 (k1 k2 ke : String) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RIF k1 k2 ke 2 ⟨eα,ep⟩) "env" ({destination_name := "fwd1", content := c} : Message) (n+3)
    = cfgReturns (RIF k1 k2 ke 2 ⟨eα,ep⟩) "fwd1" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RIF, idealPinsRst, idealWires, Router.route, KEIdealR, KESimR, DummyPt, DummyAdv, DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin, Pin.invoke, changePinOfName, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelI_2_fwd2 (k1 k2 ke : String) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RIF k1 k2 ke 2 ⟨eα,ep⟩) "env" ({destination_name := "fwd2", content := c} : Message) (n+3)
    = cfgReturns (RIF k1 k2 ke 2 ⟨eα,ep⟩) "fwd2" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RIF, idealPinsRst, idealWires, Router.route, KEIdealR, KESimR, DummyPt, DummyAdv, DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin, Pin.invoke, changePinOfName, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelI_3_pt1 (k1 k2 ke : String) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RIF k1 k2 ke 3 ⟨eα,ep⟩) "env" ({destination_name := "pt1", content := c} : Message) (n+3)
    = cfgReturns (RIF k1 k2 ke 3 ⟨eα,ep⟩) "pt1" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RIF, idealPinsRst, idealWires, Router.route, KEIdealR, KESimR, DummyPt, DummyAdv, DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin, Pin.invoke, changePinOfName, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelI_3_pt2 (k1 k2 ke : String) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RIF k1 k2 ke 3 ⟨eα,ep⟩) "env" ({destination_name := "pt2", content := c} : Message) (n+3)
    = cfgReturns (RIF k1 k2 ke 3 ⟨eα,ep⟩) "pt2" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RIF, idealPinsRst, idealWires, Router.route, KEIdealR, KESimR, DummyPt, DummyAdv, DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin, Pin.invoke, changePinOfName, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelI_3_fwd1 (k1 k2 ke : String) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RIF k1 k2 ke 3 ⟨eα,ep⟩) "env" ({destination_name := "fwd1", content := c} : Message) (n+3)
    = cfgReturns (RIF k1 k2 ke 3 ⟨eα,ep⟩) "fwd1" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RIF, idealPinsRst, idealWires, Router.route, KEIdealR, KESimR, DummyPt, DummyAdv, DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin, Pin.invoke, changePinOfName, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelI_4_pt1 (k1 k2 ke : String) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RIF k1 k2 ke 4 ⟨eα,ep⟩) "env" ({destination_name := "pt1", content := c} : Message) (n+3)
    = cfgReturns (RIF k1 k2 ke 4 ⟨eα,ep⟩) "pt1" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RIF, idealPinsRst, idealWires, Router.route, KEIdealR, KESimR, DummyPt, DummyAdv, DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin, Pin.invoke, changePinOfName, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelI_4_pt2 (k1 k2 ke : String) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RIF k1 k2 ke 4 ⟨eα,ep⟩) "env" ({destination_name := "pt2", content := c} : Message) (n+3)
    = cfgReturns (RIF k1 k2 ke 4 ⟨eα,ep⟩) "pt2" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RIF, idealPinsRst, idealWires, Router.route, KEIdealR, KESimR, DummyPt, DummyAdv, DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin, Pin.invoke, changePinOfName, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelI_4_fwd1 (k1 k2 ke : String) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RIF k1 k2 ke 4 ⟨eα,ep⟩) "env" ({destination_name := "fwd1", content := c} : Message) (n+3)
    = cfgReturns (RIF k1 k2 ke 4 ⟨eα,ep⟩) "fwd1" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RIF, idealPinsRst, idealWires, Router.route, KEIdealR, KESimR, DummyPt, DummyAdv, DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin, Pin.invoke, changePinOfName, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelI_4_fwd2 (k1 k2 ke : String) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RIF k1 k2 ke 4 ⟨eα,ep⟩) "env" ({destination_name := "fwd2", content := c} : Message) (n+3)
    = cfgReturns (RIF k1 k2 ke 4 ⟨eα,ep⟩) "fwd2" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RIF, idealPinsRst, idealWires, Router.route, KEIdealR, KESimR, DummyPt, DummyAdv, DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin, Pin.invoke, changePinOfName, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]


-- ===========================================================================
-- "other" peels (destination not a protocol pin: bounce to env) and stuck.
-- ===========================================================================

theorem peelR_other (q1 q2 : Nat) (i : ℕ) (eα : Type) (ep : Pin eα) (henv : ep.name = "env")
    (md mc : String) (h1 : md ≠ "experiment") (h2 : md ≠ "pt1") (h3 : md ≠ "pt2")
    (h4 : md ≠ "fwd1") (h5 : md ≠ "fwd2") (h6 : md ≠ "env") (n : ℕ) :
    cfgReturns (RRF q1 q2 i ⟨eα,ep⟩) "env" ({destination_name := md, content := mc} : Message) (n+1)
    = cfgReturns (RRF q1 q2 i ⟨eα,ep⟩) "env"
        (destinationEnvMessage ({destination_name := md, content := mc} : Message)) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RRF, realPinsFst, realWires, Router.route, Pt1F, Pt2F, Forwarder, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, h1, h2, h3, h4, h5, h6, Finset.mem_insert, Finset.mem_singleton, bind, PMF.pure_bind]

theorem peelI_other (k1 k2 ke : String) (i : ℕ) (eα : Type) (ep : Pin eα) (henv : ep.name = "env")
    (md mc : String) (h1 : md ≠ "experiment") (h2 : md ≠ "pt1") (h3 : md ≠ "pt2")
    (h4 : md ≠ "fwd1") (h5 : md ≠ "fwd2") (h6 : md ≠ "env") (n : ℕ) :
    cfgReturns (RIF k1 k2 ke i ⟨eα,ep⟩) "env" ({destination_name := md, content := mc} : Message) (n+1)
    = cfgReturns (RIF k1 k2 ke i ⟨eα,ep⟩) "env"
        (destinationEnvMessage ({destination_name := md, content := mc} : Message)) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RIF, idealPinsRst, idealWires, Router.route, KEIdealR, KESimR, DummyPt, DummyAdv, DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, h1, h2, h3, h4, h5, h6, Finset.mem_insert, Finset.mem_singleton, bind, PMF.pure_bind]

theorem route_stuck_real (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (hne : ep.name ≠ "env")
    (m : Message) (hm : m.destination_name = "env") :
    Router.route (RRF q1 q2 0 ⟨eα,ep⟩) "experiment" m
    = PMF.pure (RRF q1 q2 0 ⟨eα,ep⟩, "experiment", destinationEnvMessage m) := by
  simp [RRF, realPinsFst, realWires, Router.route, Pin.invoke, changePinOfName, destinationEnvMessage, hm, hne, List.find?, List.map, bind, PMF.pure_bind]

theorem route_stuck_ideal (k1 k2 ke : String) (eα : Type) (ep : Pin eα) (hne : ep.name ≠ "env")
    (m : Message) (hm : m.destination_name = "env") :
    Router.route (RIF k1 k2 ke 0 ⟨eα,ep⟩) "experiment" m
    = PMF.pure (RIF k1 k2 ke 0 ⟨eα,ep⟩, "experiment", destinationEnvMessage m) := by
  simp [RIF, idealPinsRst, idealWires, Router.route, Pin.invoke, changePinOfName, destinationEnvMessage, DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin, hm, hne, List.find?, List.map, bind, PMF.pure_bind]

theorem cfgReturns_stuck_real (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (hne : ep.name ≠ "env") :
    ∀ (k : ℕ) (m : Message), m.destination_name = "env"
      → cfgReturns (RRF q1 q2 0 ⟨eα,ep⟩) "experiment" m k = 0 := by
  intro k
  induction k with
  | zero => intro m hm; exact cfgReturns_zero_nexp _ _ _ (by rw [hm]; decide)
  | succ n ih =>
    intro m hm
    rw [cfgReturns_pure_step (by rw [hm]; decide) (route_stuck_real q1 q2 eα ep hne m hm)]
    exact ih _ (by simp [destinationEnvMessage])

theorem cfgReturns_stuck_ideal (k1 k2 ke : String) (eα : Type) (ep : Pin eα) (hne : ep.name ≠ "env") :
    ∀ (k : ℕ) (m : Message), m.destination_name = "env"
      → cfgReturns (RIF k1 k2 ke 0 ⟨eα,ep⟩) "experiment" m k = 0 := by
  intro k
  induction k with
  | zero => intro m hm; exact cfgReturns_zero_nexp _ _ _ (by rw [hm]; decide)
  | succ n ih =>
    intro m hm
    rw [cfgReturns_pure_step (by rw [hm]; decide) (route_stuck_ideal k1 k2 ke eα ep hne m hm)]
    exact ih _ (by simp [destinationEnvMessage])

theorem RTE_stuck_real (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (hne : ep.name ≠ "env") :
    ReturnsToExperiment (RRF q1 q2 0 ⟨eα,ep⟩) "experiment" startMessage = 0 := by
  rw [ReturnsToExperiment_eq_iSup]
  have h : ∀ k, cfgReturns (RRF q1 q2 0 ⟨eα,ep⟩) "experiment" startMessage k = 0 :=
    fun k => cfgReturns_stuck_real q1 q2 eα ep hne k startMessage (by simp [startMessage])
  simp [h]

theorem RTE_stuck_ideal (k1 k2 ke : String) (eα : Type) (ep : Pin eα) (hne : ep.name ≠ "env") :
    ReturnsToExperiment (RIF k1 k2 ke 0 ⟨eα,ep⟩) "experiment" startMessage = 0 := by
  rw [ReturnsToExperiment_eq_iSup]
  have h : ∀ k, cfgReturns (RIF k1 k2 ke 0 ⟨eα,ep⟩) "experiment" startMessage k = 0 :=
    fun k => cfgReturns_stuck_ideal k1 k2 ke eα ep hne k startMessage (by simp [startMessage])
  simp [h]

-- ===========================================================================
-- Bisimulation: detReal (q1,q2) and G with matching keys return with equal prob.
-- ===========================================================================

theorem step_bound (rR rI rR' rI' : Router) (sR sI sR' sI' : String)
    (mR mI mR' mI' : Message) (aR aI n : ℕ)
    (hpeelR : ∀ j, cfgReturns rR sR mR (j + aR) = cfgReturns rR' sR' mR' j)
    (hpeelI : ∀ j, cfgReturns rI sI mI (j + aI) = cfgReturns rI' sI' mI' j)
    (hih : cfgReturns rR' sR' mR' n ≤ ReturnsToExperiment rI' sI' mI') :
    cfgReturns rR sR mR n ≤ ReturnsToExperiment rI sI mI := by
  calc cfgReturns rR sR mR n
      ≤ cfgReturns rR sR mR (n + aR) := cfgReturns_le_add _ _ _ _ _
    _ = cfgReturns rR' sR' mR' n := hpeelR n
    _ ≤ ReturnsToExperiment rI' sI' mI' := hih
    _ = ReturnsToExperiment rI sI mI := (ReturnsToExperiment_of_peel aI hpeelI).symm

theorem half_le (q1 q2 : Nat) : ∀ (k i : ℕ) (eα : Type) (ep : Pin eα) (s : String) (m : Message),
    ep.name = "env" → m.destination_name = "env" → sOK s → i ≤ 4 →
    cfgReturns (RRF q1 q2 i ⟨eα,ep⟩) s m k
      ≤ ReturnsToExperiment (RIF (pwr "g" q1) (pwr "g" q2) (pwr (pwr "g" q2) q1) i ⟨eα,ep⟩) s m := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i eα ep s m henv hm hs hi
    cases k with
    | zero => rw [cfgReturns_zero_nexp _ _ _ (by rw [hm]; decide)]; exact zero_le
    | succ n =>
      rw [cfgReturns_env_deliver_gen _ _ _ (by rw [hm]; decide) (delivReal q1 q2 i hi eα ep s m henv hm hs) n,
          ReturnsToExperiment_env_deliver_gen _ _ _ (by rw [hm]; decide) (delivIdeal (pwr "g" q1) (pwr "g" q2) (pwr (pwr "g" q2) q1) i hi eα ep s m henv hm hs)]
      apply ENNReal.tsum_le_tsum
      intro x
      apply mul_le_mul_left'
      obtain ⟨⟨md, mc⟩, ns⟩ := x
      set ep2 := envStep ep ns with hep2
      have hname2 : ep2.name = "env" := by rw [hep2]; exact envStep_name ep ns henv
      rcases i with _|_|_|_|_|i
      · -- phase 0
        by_cases h_exp : md = "experiment"
        · subst h_exp
          rw [cfgReturns_exp _ _ _ rfl, ReturnsToExperiment_eq_iSup]
          exact le_iSup_of_le 0 (le_of_eq (cfgReturns_exp _ _ _ rfl 0).symm)
        by_cases h_env : md = "env"
        · subst h_env
          exact ih n (Nat.lt_succ_self n) 0 eα ep2 "env" ⟨"env", mc⟩ hname2 rfl sOK_env (by omega)
        by_cases h_pt1 : md = "pt1"
        · subst h_pt1
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 2 4 n
            (peelR_0_pt1 q1 q2 eα ep2 hname2 mc) (peelI_0_pt1 _ _ _ eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 1 eα ep2 "fwd1" ⟨"env", string2selfdelimitingString "pt1" ++ toString ({destination_name := "pt2", content := pwr "g" q1} : Message)⟩ hname2 rfl sOK_fwd1 (by omega))
        by_cases h_pt2 : md = "pt2"
        · subst h_pt2
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 3 n
            (peelR_0_pt2 q1 q2 eα ep2 hname2 mc) (peelI_0_pt2 _ _ _ eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 0 eα ep2 "pt2" ⟨"env", contentError⟩ hname2 rfl sOK_pt2 (by omega))
        by_cases h_fwd1 : md = "fwd1"
        · subst h_fwd1
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 3 n
            (peelR_0_fwd1 q1 q2 eα ep2 hname2 mc) (peelI_0_fwd1 _ _ _ eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 0 eα ep2 "fwd1" ⟨"env", contentError⟩ hname2 rfl sOK_fwd1 (by omega))
        by_cases h_fwd2 : md = "fwd2"
        · subst h_fwd2
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 3 n
            (peelR_0_fwd2 q1 q2 eα ep2 hname2 mc) (peelI_0_fwd2 _ _ _ eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 0 eα ep2 "fwd2" ⟨"env", contentError⟩ hname2 rfl sOK_fwd2 (by omega))
        · exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 1 n
            (peelR_other q1 q2 0 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env) (peelI_other _ _ _ 0 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env)
            (ih n (Nat.lt_succ_self n) 0 eα ep2 "env" (destinationEnvMessage ⟨md, mc⟩) hname2 (by simp [destinationEnvMessage]) sOK_env (by omega))
      · -- phase 1
        by_cases h_exp : md = "experiment"
        · subst h_exp
          rw [cfgReturns_exp _ _ _ rfl, ReturnsToExperiment_eq_iSup]
          exact le_iSup_of_le 0 (le_of_eq (cfgReturns_exp _ _ _ rfl 0).symm)
        by_cases h_env : md = "env"
        · subst h_env
          exact ih n (Nat.lt_succ_self n) 1 eα ep2 "env" ⟨"env", mc⟩ hname2 rfl sOK_env (by omega)
        by_cases h_pt1 : md = "pt1"
        · subst h_pt1
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 3 n
            (peelR_1_pt1 q1 q2 eα ep2 hname2 mc) (peelI_1_pt1 _ _ _ eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 1 eα ep2 "pt1" ⟨"env", contentError⟩ hname2 rfl sOK_pt1 (by omega))
        by_cases h_pt2 : md = "pt2"
        · subst h_pt2
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 3 n
            (peelR_1_pt2 q1 q2 eα ep2 hname2 mc) (peelI_1_pt2 _ _ _ eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 1 eα ep2 "pt2" ⟨"env", contentError⟩ hname2 rfl sOK_pt2 (by omega))
        by_cases h_fwd1 : md = "fwd1"
        · subst h_fwd1
          refine step_bound _ _ _ _ _ _ _ _ _ _ _ _ 2 4 n
            (peelR_1_fwd1 q1 q2 eα ep2 hname2 mc) (peelI_1_fwd1 _ _ _ eα ep2 hname2 mc) ?_
          rw [show pwr (pwr "g" q1) q2 = pwr (pwr "g" q2) q1 from pwr_comm "g" q1 q2]
          exact ih n (Nat.lt_succ_self n) 2 eα ep2 "pt2" ⟨"env", pwr (pwr "g" q2) q1⟩ hname2 rfl sOK_pt2 (by omega)
        by_cases h_fwd2 : md = "fwd2"
        · subst h_fwd2
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 3 n
            (peelR_1_fwd2 q1 q2 eα ep2 hname2 mc) (peelI_1_fwd2 _ _ _ eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 1 eα ep2 "fwd2" ⟨"env", contentError⟩ hname2 rfl sOK_fwd2 (by omega))
        · exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 1 n
            (peelR_other q1 q2 1 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env) (peelI_other _ _ _ 1 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env)
            (ih n (Nat.lt_succ_self n) 1 eα ep2 "env" (destinationEnvMessage ⟨md, mc⟩) hname2 (by simp [destinationEnvMessage]) sOK_env (by omega))
      · -- phase 2
        by_cases h_exp : md = "experiment"
        · subst h_exp
          rw [cfgReturns_exp _ _ _ rfl, ReturnsToExperiment_eq_iSup]
          exact le_iSup_of_le 0 (le_of_eq (cfgReturns_exp _ _ _ rfl 0).symm)
        by_cases h_env : md = "env"
        · subst h_env
          exact ih n (Nat.lt_succ_self n) 2 eα ep2 "env" ⟨"env", mc⟩ hname2 rfl sOK_env (by omega)
        by_cases h_pt1 : md = "pt1"
        · subst h_pt1
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 3 n
            (peelR_2_pt1 q1 q2 eα ep2 hname2 mc) (peelI_2_pt1 _ _ _ eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 2 eα ep2 "pt1" ⟨"env", contentError⟩ hname2 rfl sOK_pt1 (by omega))
        by_cases h_pt2 : md = "pt2"
        · subst h_pt2
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 2 4 n
            (peelR_2_pt2 q1 q2 eα ep2 hname2 mc) (peelI_2_pt2 _ _ _ eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 3 eα ep2 "fwd2" ⟨"env", string2selfdelimitingString "pt2" ++ toString ({destination_name := "pt1", content := pwr "g" q2} : Message)⟩ hname2 rfl sOK_fwd2 (by omega))
        by_cases h_fwd1 : md = "fwd1"
        · subst h_fwd1
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 3 n
            (peelR_2_fwd1 q1 q2 eα ep2 hname2 mc) (peelI_2_fwd1 _ _ _ eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 2 eα ep2 "fwd1" ⟨"env", contentError⟩ hname2 rfl sOK_fwd1 (by omega))
        by_cases h_fwd2 : md = "fwd2"
        · subst h_fwd2
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 3 n
            (peelR_2_fwd2 q1 q2 eα ep2 hname2 mc) (peelI_2_fwd2 _ _ _ eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 2 eα ep2 "fwd2" ⟨"env", contentError⟩ hname2 rfl sOK_fwd2 (by omega))
        · exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 1 n
            (peelR_other q1 q2 2 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env) (peelI_other _ _ _ 2 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env)
            (ih n (Nat.lt_succ_self n) 2 eα ep2 "env" (destinationEnvMessage ⟨md, mc⟩) hname2 (by simp [destinationEnvMessage]) sOK_env (by omega))
      · -- phase 3
        by_cases h_exp : md = "experiment"
        · subst h_exp
          rw [cfgReturns_exp _ _ _ rfl, ReturnsToExperiment_eq_iSup]
          exact le_iSup_of_le 0 (le_of_eq (cfgReturns_exp _ _ _ rfl 0).symm)
        by_cases h_env : md = "env"
        · subst h_env
          exact ih n (Nat.lt_succ_self n) 3 eα ep2 "env" ⟨"env", mc⟩ hname2 rfl sOK_env (by omega)
        by_cases h_pt1 : md = "pt1"
        · subst h_pt1
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 3 n
            (peelR_3_pt1 q1 q2 eα ep2 hname2 mc) (peelI_3_pt1 _ _ _ eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 3 eα ep2 "pt1" ⟨"env", contentError⟩ hname2 rfl sOK_pt1 (by omega))
        by_cases h_pt2 : md = "pt2"
        · subst h_pt2
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 3 n
            (peelR_3_pt2 q1 q2 eα ep2 hname2 mc) (peelI_3_pt2 _ _ _ eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 3 eα ep2 "pt2" ⟨"env", contentError⟩ hname2 rfl sOK_pt2 (by omega))
        by_cases h_fwd1 : md = "fwd1"
        · subst h_fwd1
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 3 n
            (peelR_3_fwd1 q1 q2 eα ep2 hname2 mc) (peelI_3_fwd1 _ _ _ eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 3 eα ep2 "fwd1" ⟨"env", contentError⟩ hname2 rfl sOK_fwd1 (by omega))
        by_cases h_fwd2 : md = "fwd2"
        · subst h_fwd2
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 2 4 n
            (peelR_3_fwd2 q1 q2 eα ep2 hname2 mc) (peelI_3_fwd2 _ _ _ eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 4 eα ep2 "pt1" ⟨"env", pwr (pwr "g" q2) q1⟩ hname2 rfl sOK_pt1 (by omega))
        · exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 1 n
            (peelR_other q1 q2 3 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env) (peelI_other _ _ _ 3 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env)
            (ih n (Nat.lt_succ_self n) 3 eα ep2 "env" (destinationEnvMessage ⟨md, mc⟩) hname2 (by simp [destinationEnvMessage]) sOK_env (by omega))
      · -- phase 4
        by_cases h_exp : md = "experiment"
        · subst h_exp
          rw [cfgReturns_exp _ _ _ rfl, ReturnsToExperiment_eq_iSup]
          exact le_iSup_of_le 0 (le_of_eq (cfgReturns_exp _ _ _ rfl 0).symm)
        by_cases h_env : md = "env"
        · subst h_env
          exact ih n (Nat.lt_succ_self n) 4 eα ep2 "env" ⟨"env", mc⟩ hname2 rfl sOK_env (by omega)
        by_cases h_pt1 : md = "pt1"
        · subst h_pt1
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 3 n
            (peelR_4_pt1 q1 q2 eα ep2 hname2 mc) (peelI_4_pt1 _ _ _ eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 4 eα ep2 "pt1" ⟨"env", contentError⟩ hname2 rfl sOK_pt1 (by omega))
        by_cases h_pt2 : md = "pt2"
        · subst h_pt2
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 3 n
            (peelR_4_pt2 q1 q2 eα ep2 hname2 mc) (peelI_4_pt2 _ _ _ eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 4 eα ep2 "pt2" ⟨"env", contentError⟩ hname2 rfl sOK_pt2 (by omega))
        by_cases h_fwd1 : md = "fwd1"
        · subst h_fwd1
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 3 n
            (peelR_4_fwd1 q1 q2 eα ep2 hname2 mc) (peelI_4_fwd1 _ _ _ eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 4 eα ep2 "fwd1" ⟨"env", contentError⟩ hname2 rfl sOK_fwd1 (by omega))
        by_cases h_fwd2 : md = "fwd2"
        · subst h_fwd2
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 3 n
            (peelR_4_fwd2 q1 q2 eα ep2 hname2 mc) (peelI_4_fwd2 _ _ _ eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 4 eα ep2 "fwd2" ⟨"env", contentError⟩ hname2 rfl sOK_fwd2 (by omega))
        · exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 1 n
            (peelR_other q1 q2 4 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env) (peelI_other _ _ _ 4 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env)
            (ih n (Nat.lt_succ_self n) 4 eα ep2 "env" (destinationEnvMessage ⟨md, mc⟩) hname2 (by simp [destinationEnvMessage]) sOK_env (by omega))
      · exact absurd hi (by omega)

theorem half_le' (q1 q2 : Nat) : ∀ (k i : ℕ) (eα : Type) (ep : Pin eα) (s : String) (m : Message),
    ep.name = "env" → m.destination_name = "env" → sOK s → i ≤ 4 →
    cfgReturns (RIF (pwr "g" q1) (pwr "g" q2) (pwr (pwr "g" q2) q1) i ⟨eα,ep⟩) s m k
      ≤ ReturnsToExperiment (RRF q1 q2 i ⟨eα,ep⟩) s m := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i eα ep s m henv hm hs hi
    cases k with
    | zero => rw [cfgReturns_zero_nexp _ _ _ (by rw [hm]; decide)]; exact zero_le
    | succ n =>
      rw [cfgReturns_env_deliver_gen _ _ _ (by rw [hm]; decide) (delivIdeal (pwr "g" q1) (pwr "g" q2) (pwr (pwr "g" q2) q1) i hi eα ep s m henv hm hs) n,
          ReturnsToExperiment_env_deliver_gen _ _ _ (by rw [hm]; decide) (delivReal q1 q2 i hi eα ep s m henv hm hs)]
      apply ENNReal.tsum_le_tsum
      intro x
      apply mul_le_mul_left'
      obtain ⟨⟨md, mc⟩, ns⟩ := x
      set ep2 := envStep ep ns with hep2
      have hname2 : ep2.name = "env" := by rw [hep2]; exact envStep_name ep ns henv
      rcases i with _|_|_|_|_|i
      · -- phase 0
        by_cases h_exp : md = "experiment"
        · subst h_exp
          rw [cfgReturns_exp _ _ _ rfl, ReturnsToExperiment_eq_iSup]
          exact le_iSup_of_le 0 (le_of_eq (cfgReturns_exp _ _ _ rfl 0).symm)
        by_cases h_env : md = "env"
        · subst h_env
          exact ih n (Nat.lt_succ_self n) 0 eα ep2 "env" ⟨"env", mc⟩ hname2 rfl sOK_env (by omega)
        by_cases h_pt1 : md = "pt1"
        · subst h_pt1
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 4 2 n
            (peelI_0_pt1 _ _ _ eα ep2 hname2 mc) (peelR_0_pt1 q1 q2 eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 1 eα ep2 "fwd1" ⟨"env", string2selfdelimitingString "pt1" ++ toString ({destination_name := "pt2", content := pwr "g" q1} : Message)⟩ hname2 rfl sOK_fwd1 (by omega))
        by_cases h_pt2 : md = "pt2"
        · subst h_pt2
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 3 1 n
            (peelI_0_pt2 _ _ _ eα ep2 hname2 mc) (peelR_0_pt2 q1 q2 eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 0 eα ep2 "pt2" ⟨"env", contentError⟩ hname2 rfl sOK_pt2 (by omega))
        by_cases h_fwd1 : md = "fwd1"
        · subst h_fwd1
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 3 1 n
            (peelI_0_fwd1 _ _ _ eα ep2 hname2 mc) (peelR_0_fwd1 q1 q2 eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 0 eα ep2 "fwd1" ⟨"env", contentError⟩ hname2 rfl sOK_fwd1 (by omega))
        by_cases h_fwd2 : md = "fwd2"
        · subst h_fwd2
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 3 1 n
            (peelI_0_fwd2 _ _ _ eα ep2 hname2 mc) (peelR_0_fwd2 q1 q2 eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 0 eα ep2 "fwd2" ⟨"env", contentError⟩ hname2 rfl sOK_fwd2 (by omega))
        · exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 1 n
            (peelI_other _ _ _ 0 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env) (peelR_other q1 q2 0 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env)
            (ih n (Nat.lt_succ_self n) 0 eα ep2 "env" (destinationEnvMessage ⟨md, mc⟩) hname2 (by simp [destinationEnvMessage]) sOK_env (by omega))
      · -- phase 1
        by_cases h_exp : md = "experiment"
        · subst h_exp
          rw [cfgReturns_exp _ _ _ rfl, ReturnsToExperiment_eq_iSup]
          exact le_iSup_of_le 0 (le_of_eq (cfgReturns_exp _ _ _ rfl 0).symm)
        by_cases h_env : md = "env"
        · subst h_env
          exact ih n (Nat.lt_succ_self n) 1 eα ep2 "env" ⟨"env", mc⟩ hname2 rfl sOK_env (by omega)
        by_cases h_pt1 : md = "pt1"
        · subst h_pt1
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 3 1 n
            (peelI_1_pt1 _ _ _ eα ep2 hname2 mc) (peelR_1_pt1 q1 q2 eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 1 eα ep2 "pt1" ⟨"env", contentError⟩ hname2 rfl sOK_pt1 (by omega))
        by_cases h_pt2 : md = "pt2"
        · subst h_pt2
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 3 1 n
            (peelI_1_pt2 _ _ _ eα ep2 hname2 mc) (peelR_1_pt2 q1 q2 eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 1 eα ep2 "pt2" ⟨"env", contentError⟩ hname2 rfl sOK_pt2 (by omega))
        by_cases h_fwd1 : md = "fwd1"
        · subst h_fwd1
          refine step_bound _ _ _ _ _ _ _ _ _ _ _ _ 4 2 n
            (peelI_1_fwd1 _ _ _ eα ep2 hname2 mc) (peelR_1_fwd1 q1 q2 eα ep2 hname2 mc) ?_
          rw [show pwr (pwr "g" q1) q2 = pwr (pwr "g" q2) q1 from pwr_comm "g" q1 q2]
          exact ih n (Nat.lt_succ_self n) 2 eα ep2 "pt2" ⟨"env", pwr (pwr "g" q2) q1⟩ hname2 rfl sOK_pt2 (by omega)
        by_cases h_fwd2 : md = "fwd2"
        · subst h_fwd2
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 3 1 n
            (peelI_1_fwd2 _ _ _ eα ep2 hname2 mc) (peelR_1_fwd2 q1 q2 eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 1 eα ep2 "fwd2" ⟨"env", contentError⟩ hname2 rfl sOK_fwd2 (by omega))
        · exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 1 n
            (peelI_other _ _ _ 1 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env) (peelR_other q1 q2 1 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env)
            (ih n (Nat.lt_succ_self n) 1 eα ep2 "env" (destinationEnvMessage ⟨md, mc⟩) hname2 (by simp [destinationEnvMessage]) sOK_env (by omega))
      · -- phase 2
        by_cases h_exp : md = "experiment"
        · subst h_exp
          rw [cfgReturns_exp _ _ _ rfl, ReturnsToExperiment_eq_iSup]
          exact le_iSup_of_le 0 (le_of_eq (cfgReturns_exp _ _ _ rfl 0).symm)
        by_cases h_env : md = "env"
        · subst h_env
          exact ih n (Nat.lt_succ_self n) 2 eα ep2 "env" ⟨"env", mc⟩ hname2 rfl sOK_env (by omega)
        by_cases h_pt1 : md = "pt1"
        · subst h_pt1
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 3 1 n
            (peelI_2_pt1 _ _ _ eα ep2 hname2 mc) (peelR_2_pt1 q1 q2 eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 2 eα ep2 "pt1" ⟨"env", contentError⟩ hname2 rfl sOK_pt1 (by omega))
        by_cases h_pt2 : md = "pt2"
        · subst h_pt2
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 4 2 n
            (peelI_2_pt2 _ _ _ eα ep2 hname2 mc) (peelR_2_pt2 q1 q2 eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 3 eα ep2 "fwd2" ⟨"env", string2selfdelimitingString "pt2" ++ toString ({destination_name := "pt1", content := pwr "g" q2} : Message)⟩ hname2 rfl sOK_fwd2 (by omega))
        by_cases h_fwd1 : md = "fwd1"
        · subst h_fwd1
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 3 1 n
            (peelI_2_fwd1 _ _ _ eα ep2 hname2 mc) (peelR_2_fwd1 q1 q2 eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 2 eα ep2 "fwd1" ⟨"env", contentError⟩ hname2 rfl sOK_fwd1 (by omega))
        by_cases h_fwd2 : md = "fwd2"
        · subst h_fwd2
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 3 1 n
            (peelI_2_fwd2 _ _ _ eα ep2 hname2 mc) (peelR_2_fwd2 q1 q2 eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 2 eα ep2 "fwd2" ⟨"env", contentError⟩ hname2 rfl sOK_fwd2 (by omega))
        · exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 1 n
            (peelI_other _ _ _ 2 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env) (peelR_other q1 q2 2 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env)
            (ih n (Nat.lt_succ_self n) 2 eα ep2 "env" (destinationEnvMessage ⟨md, mc⟩) hname2 (by simp [destinationEnvMessage]) sOK_env (by omega))
      · -- phase 3
        by_cases h_exp : md = "experiment"
        · subst h_exp
          rw [cfgReturns_exp _ _ _ rfl, ReturnsToExperiment_eq_iSup]
          exact le_iSup_of_le 0 (le_of_eq (cfgReturns_exp _ _ _ rfl 0).symm)
        by_cases h_env : md = "env"
        · subst h_env
          exact ih n (Nat.lt_succ_self n) 3 eα ep2 "env" ⟨"env", mc⟩ hname2 rfl sOK_env (by omega)
        by_cases h_pt1 : md = "pt1"
        · subst h_pt1
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 3 1 n
            (peelI_3_pt1 _ _ _ eα ep2 hname2 mc) (peelR_3_pt1 q1 q2 eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 3 eα ep2 "pt1" ⟨"env", contentError⟩ hname2 rfl sOK_pt1 (by omega))
        by_cases h_pt2 : md = "pt2"
        · subst h_pt2
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 3 1 n
            (peelI_3_pt2 _ _ _ eα ep2 hname2 mc) (peelR_3_pt2 q1 q2 eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 3 eα ep2 "pt2" ⟨"env", contentError⟩ hname2 rfl sOK_pt2 (by omega))
        by_cases h_fwd1 : md = "fwd1"
        · subst h_fwd1
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 3 1 n
            (peelI_3_fwd1 _ _ _ eα ep2 hname2 mc) (peelR_3_fwd1 q1 q2 eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 3 eα ep2 "fwd1" ⟨"env", contentError⟩ hname2 rfl sOK_fwd1 (by omega))
        by_cases h_fwd2 : md = "fwd2"
        · subst h_fwd2
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 4 2 n
            (peelI_3_fwd2 _ _ _ eα ep2 hname2 mc) (peelR_3_fwd2 q1 q2 eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 4 eα ep2 "pt1" ⟨"env", pwr (pwr "g" q2) q1⟩ hname2 rfl sOK_pt1 (by omega))
        · exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 1 n
            (peelI_other _ _ _ 3 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env) (peelR_other q1 q2 3 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env)
            (ih n (Nat.lt_succ_self n) 3 eα ep2 "env" (destinationEnvMessage ⟨md, mc⟩) hname2 (by simp [destinationEnvMessage]) sOK_env (by omega))
      · -- phase 4
        by_cases h_exp : md = "experiment"
        · subst h_exp
          rw [cfgReturns_exp _ _ _ rfl, ReturnsToExperiment_eq_iSup]
          exact le_iSup_of_le 0 (le_of_eq (cfgReturns_exp _ _ _ rfl 0).symm)
        by_cases h_env : md = "env"
        · subst h_env
          exact ih n (Nat.lt_succ_self n) 4 eα ep2 "env" ⟨"env", mc⟩ hname2 rfl sOK_env (by omega)
        by_cases h_pt1 : md = "pt1"
        · subst h_pt1
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 3 1 n
            (peelI_4_pt1 _ _ _ eα ep2 hname2 mc) (peelR_4_pt1 q1 q2 eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 4 eα ep2 "pt1" ⟨"env", contentError⟩ hname2 rfl sOK_pt1 (by omega))
        by_cases h_pt2 : md = "pt2"
        · subst h_pt2
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 3 1 n
            (peelI_4_pt2 _ _ _ eα ep2 hname2 mc) (peelR_4_pt2 q1 q2 eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 4 eα ep2 "pt2" ⟨"env", contentError⟩ hname2 rfl sOK_pt2 (by omega))
        by_cases h_fwd1 : md = "fwd1"
        · subst h_fwd1
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 3 1 n
            (peelI_4_fwd1 _ _ _ eα ep2 hname2 mc) (peelR_4_fwd1 q1 q2 eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 4 eα ep2 "fwd1" ⟨"env", contentError⟩ hname2 rfl sOK_fwd1 (by omega))
        by_cases h_fwd2 : md = "fwd2"
        · subst h_fwd2
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 3 1 n
            (peelI_4_fwd2 _ _ _ eα ep2 hname2 mc) (peelR_4_fwd2 q1 q2 eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 4 eα ep2 "fwd2" ⟨"env", contentError⟩ hname2 rfl sOK_fwd2 (by omega))
        · exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 1 n
            (peelI_other _ _ _ 4 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env) (peelR_other q1 q2 4 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env)
            (ih n (Nat.lt_succ_self n) 4 eα ep2 "env" (destinationEnvMessage ⟨md, mc⟩) hname2 (by simp [destinationEnvMessage]) sOK_env (by omega))
      · exact absurd hi (by omega)

theorem detReal_eq_G (env : SPin) (q1 q2 : Nat) :
    detReal env q1 q2 = G env (pwr "g" q1) (pwr "g" q2) (pwr (pwr "g" q2) q1) := by
  obtain ⟨eα, ep⟩ := env
  show ReturnsToExperiment (RRF q1 q2 0 ⟨eα,ep⟩) "experiment" startMessage
     = ReturnsToExperiment (RIF (pwr "g" q1) (pwr "g" q2) (pwr (pwr "g" q2) q1) 0 ⟨eα,ep⟩) "experiment" startMessage
  by_cases hn : ep.name = "env"
  · apply le_antisymm
    · rw [ReturnsToExperiment_eq_iSup (RRF q1 q2 0 ⟨eα,ep⟩)]
      exact iSup_le (fun k => half_le q1 q2 k 0 eα ep "experiment" startMessage hn
        (by simp [startMessage]) sOK_experiment (by omega))
    · rw [ReturnsToExperiment_eq_iSup (RIF (pwr "g" q1) (pwr "g" q2) (pwr (pwr "g" q2) q1) 0 ⟨eα,ep⟩)]
      exact iSup_le (fun k => half_le' q1 q2 k 0 eα ep "experiment" startMessage hn
        (by simp [startMessage]) sOK_experiment (by omega))
  · rw [RTE_stuck_real q1 q2 eα ep hn, RTE_stuck_ideal _ _ _ eα ep hn]

-- ===========================================================================
-- G is a (sub)probability
-- ===========================================================================

theorem G_le_one (env : SPin) (k1 k2 ke : String) : G env k1 k2 ke ≤ 1 := by
  unfold G StartExperiment ReturnsToExperiment
  exact iSup_le (fun k => PMF.coe_le_one _ _)

-- ===========================================================================
-- Decomposition of the two experiments over the key distributions with the
-- common replay-acceptance function G.  (Protocol bisimulations; filled below.)
-- ===========================================================================

theorem bind_expectation {α β : Type*} (p : PMF α) (f : α → PMF β) (H : β → ENNReal) :
    ∑' t, (p.bind f) t * H t = ∑' a, p a * ∑' t, f a t * H t := by
  have h1 : ∀ t, (p.bind f) t * H t = ∑' a, p a * (f a t * H t) := by
    intro t; rw [PMF.bind_apply, ← ENNReal.tsum_mul_right]
    exact tsum_congr (fun a => (mul_assoc _ _ _))
  simp_rw [h1]
  rw [ENNReal.tsum_comm]
  exact tsum_congr (fun a => ENNReal.tsum_mul_left)

theorem pure_expectation {β : Type*} (x : β) (H : β → ENNReal) :
    ∑' t, (PMF.pure x) t * H t = H x := by
  rw [tsum_eq_single x (fun b hb => by rw [PMF.pure_apply, if_neg hb, zero_mul])]
  rw [PMF.pure_apply, if_pos rfl, one_mul]

theorem sum_distroR_G (env : SPin) :
    ∑' t : String × String × String, distroR t * G env t.1 t.2.1 t.2.2
    = ∑' q1, rnd q1 * ∑' q2, rnd q2 * detReal env q1 q2 := by
  show ∑' t, (PMF.bind rnd (fun q1 => PMF.bind rnd (fun q2 =>
        PMF.pure (pwr "g" q1, pwr "g" q2, pwr (pwr "g" q2) q1)))) t * G env t.1 t.2.1 t.2.2 = _
  rw [bind_expectation]
  refine tsum_congr (fun q1 => ?_); congr 1
  rw [bind_expectation]
  refine tsum_congr (fun q2 => ?_); congr 1
  rw [pure_expectation]
  exact (detReal_eq_G env q1 q2).symm

theorem sum_distroI_G (env : SPin) :
    ∑' t : String × String × String, distroI t * G env t.1 t.2.1 t.2.2
    = ∑' r1, rnd r1 * ∑' r2, rnd r2 * ∑' r3, rnd r3 * G env (pwr "g" r1) (pwr "g" r2) (pwr "g" r3) := by
  show ∑' t, (PMF.bind rnd (fun r1 => PMF.bind rnd (fun r2 => PMF.bind rnd (fun r3 =>
        PMF.pure (pwr "g" r1, pwr "g" r2, pwr "g" r3))))) t * G env t.1 t.2.1 t.2.2 = _
  rw [bind_expectation]
  refine tsum_congr (fun r1 => ?_); congr 1
  rw [bind_expectation]
  refine tsum_congr (fun r2 => ?_); congr 1
  rw [bind_expectation]
  refine tsum_congr (fun r3 => ?_); congr 1
  rw [pure_expectation]

-- Real-distro phase routers (rnd machines Pt1/Pt2 in the drawn states).
noncomputable def realPinsFstD (q1 q2 : Nat) (p1 : Pt1State) (p2 : Pt2State) (f1 f2 : ForwarderState)
    (env : SPin) : List SPin :=
  [ ⟨Pt1State, { name := "pt1", machine := { state := p1, func := Pt1.func } }⟩,
    ⟨Pt2State, { name := "pt2", machine := { state := p2, func := Pt2.func } }⟩,
    ⟨ForwarderState, { name := "fwd1", machine := { state := f1, func := Forwarder.func } }⟩,
    ⟨ForwarderState, { name := "fwd2", machine := { state := f2, func := Forwarder.func } }⟩,
    env ]

noncomputable def RRD (q1 q2 : Nat) (i : ℕ) (env : SPin) : Router :=
  { pins := match i with
    | 0 => realPinsFstD q1 q2 Pt1State.WaitReq1 Pt2State.WaitFwd1 ForwarderState.Init ForwarderState.Init env
    | 1 => realPinsFstD q1 q2 (Pt1State.WaitFwd2 q1) Pt2State.WaitFwd1
             (ForwarderState.WaitOK {destination_name:="pt2",content:=pwr "g" q1}) ForwarderState.Init env
    | 2 => realPinsFstD q1 q2 (Pt1State.WaitFwd2 q1) (Pt2State.WaitReq2 q2) ForwarderState.Done ForwarderState.Init env
    | 3 => realPinsFstD q1 q2 (Pt1State.WaitFwd2 q1) Pt2State.Done ForwarderState.Done
             (ForwarderState.WaitOK {destination_name:="pt1",content:=pwr "g" q2}) env
    | _ => realPinsFstD q1 q2 Pt1State.Done Pt2State.Done ForwarderState.Done ForwarderState.Done env
    , wires := realWires }

-- general env-delivery for RRD (same env.func form)
theorem delivRealD_gen (q1 q2 : Nat) (p1 : Pt1State) (p2 : Pt2State) (f1 f2 : ForwarderState)
    (eα : Type) (ep : Pin eα) (s : String) (m : Message)
    (henv : ep.name = "env") (hm : m.destination_name = "env") (hs : sOK s) :
    Router.route {pins := realPinsFstD q1 q2 p1 p2 f1 f2 ⟨eα,ep⟩, wires := realWires} s m
    = (ep.machine.func s m ep.machine.state).bind (fun x =>
        PMF.pure ({pins := realPinsFstD q1 q2 p1 p2 f1 f2 ⟨eα, envStep ep x.2⟩, wires := realWires}, "env", x.1)) := by
  rcases hs with h|h|h|h|h|h <;> subst h <;>
    simp [realPinsFstD, realWires, Router.route, Pin.invoke, envStep, changePinOfName,
      hm, henv, List.find?, List.map, Finset.mem_insert, Finset.mem_singleton, bind]

theorem delivRealD (q1 q2 : Nat) (i : ℕ) (hi : i ≤ 4) (eα : Type) (ep : Pin eα) (s : String) (m : Message)
    (henv : ep.name = "env") (hm : m.destination_name = "env") (hs : sOK s) :
    Router.route (RRD q1 q2 i ⟨eα,ep⟩) s m
    = (ep.machine.func s m ep.machine.state).bind (fun x =>
        PMF.pure (RRD q1 q2 i ⟨eα, envStep ep x.2⟩, "env", x.1)) := by
  rcases i with _|_|_|_|_|i
  · exact delivRealD_gen _ _ _ _ _ _ eα ep s m henv hm hs
  · exact delivRealD_gen _ _ _ _ _ _ eα ep s m henv hm hs
  · exact delivRealD_gen _ _ _ _ _ _ eα ep s m henv hm hs
  · exact delivRealD_gen _ _ _ _ _ _ eα ep s m henv hm hs
  · exact delivRealD_gen _ _ _ _ _ _ eα ep s m henv hm hs
  · omega

-- ===========================================================================
-- D-peels: post-draw real-distro steps (identical to RRF; Pt1/Pt2 funcs agree).
-- ===========================================================================
theorem peelRD_0_pt2 (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RRD q1 q2 0 ⟨eα,ep⟩) "env" ({destination_name := "pt2", content := c} : Message) (n+1)
    = cfgReturns (RRD q1 q2 0 ⟨eα,ep⟩) "pt2" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RRD, realPinsFstD, realWires, Router.route, Pt1, Pt2, Forwarder, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelRD_0_fwd1 (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RRD q1 q2 0 ⟨eα,ep⟩) "env" ({destination_name := "fwd1", content := c} : Message) (n+1)
    = cfgReturns (RRD q1 q2 0 ⟨eα,ep⟩) "fwd1" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RRD, realPinsFstD, realWires, Router.route, Pt1, Pt2, Forwarder, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelRD_0_fwd2 (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RRD q1 q2 0 ⟨eα,ep⟩) "env" ({destination_name := "fwd2", content := c} : Message) (n+1)
    = cfgReturns (RRD q1 q2 0 ⟨eα,ep⟩) "fwd2" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RRD, realPinsFstD, realWires, Router.route, Pt1, Pt2, Forwarder, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelRD_1_pt1 (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RRD q1 q2 1 ⟨eα,ep⟩) "env" ({destination_name := "pt1", content := c} : Message) (n+1)
    = cfgReturns (RRD q1 q2 1 ⟨eα,ep⟩) "pt1" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RRD, realPinsFstD, realWires, Router.route, Pt1, Pt2, Forwarder, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelRD_1_pt2 (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RRD q1 q2 1 ⟨eα,ep⟩) "env" ({destination_name := "pt2", content := c} : Message) (n+1)
    = cfgReturns (RRD q1 q2 1 ⟨eα,ep⟩) "pt2" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RRD, realPinsFstD, realWires, Router.route, Pt1, Pt2, Forwarder, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelRD_1_fwd2 (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RRD q1 q2 1 ⟨eα,ep⟩) "env" ({destination_name := "fwd2", content := c} : Message) (n+1)
    = cfgReturns (RRD q1 q2 1 ⟨eα,ep⟩) "fwd2" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RRD, realPinsFstD, realWires, Router.route, Pt1, Pt2, Forwarder, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelRD_2_pt1 (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RRD q1 q2 2 ⟨eα,ep⟩) "env" ({destination_name := "pt1", content := c} : Message) (n+1)
    = cfgReturns (RRD q1 q2 2 ⟨eα,ep⟩) "pt1" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RRD, realPinsFstD, realWires, Router.route, Pt1, Pt2, Forwarder, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelRD_2_fwd1 (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RRD q1 q2 2 ⟨eα,ep⟩) "env" ({destination_name := "fwd1", content := c} : Message) (n+1)
    = cfgReturns (RRD q1 q2 2 ⟨eα,ep⟩) "fwd1" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RRD, realPinsFstD, realWires, Router.route, Pt1, Pt2, Forwarder, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelRD_2_fwd2 (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RRD q1 q2 2 ⟨eα,ep⟩) "env" ({destination_name := "fwd2", content := c} : Message) (n+1)
    = cfgReturns (RRD q1 q2 2 ⟨eα,ep⟩) "fwd2" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RRD, realPinsFstD, realWires, Router.route, Pt1, Pt2, Forwarder, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelRD_3_pt1 (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RRD q1 q2 3 ⟨eα,ep⟩) "env" ({destination_name := "pt1", content := c} : Message) (n+1)
    = cfgReturns (RRD q1 q2 3 ⟨eα,ep⟩) "pt1" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RRD, realPinsFstD, realWires, Router.route, Pt1, Pt2, Forwarder, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelRD_3_pt2 (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RRD q1 q2 3 ⟨eα,ep⟩) "env" ({destination_name := "pt2", content := c} : Message) (n+1)
    = cfgReturns (RRD q1 q2 3 ⟨eα,ep⟩) "pt2" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RRD, realPinsFstD, realWires, Router.route, Pt1, Pt2, Forwarder, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelRD_3_fwd1 (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RRD q1 q2 3 ⟨eα,ep⟩) "env" ({destination_name := "fwd1", content := c} : Message) (n+1)
    = cfgReturns (RRD q1 q2 3 ⟨eα,ep⟩) "fwd1" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RRD, realPinsFstD, realWires, Router.route, Pt1, Pt2, Forwarder, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelRD_4_pt1 (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RRD q1 q2 4 ⟨eα,ep⟩) "env" ({destination_name := "pt1", content := c} : Message) (n+1)
    = cfgReturns (RRD q1 q2 4 ⟨eα,ep⟩) "pt1" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RRD, realPinsFstD, realWires, Router.route, Pt1, Pt2, Forwarder, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelRD_4_pt2 (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RRD q1 q2 4 ⟨eα,ep⟩) "env" ({destination_name := "pt2", content := c} : Message) (n+1)
    = cfgReturns (RRD q1 q2 4 ⟨eα,ep⟩) "pt2" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RRD, realPinsFstD, realWires, Router.route, Pt1, Pt2, Forwarder, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelRD_4_fwd1 (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RRD q1 q2 4 ⟨eα,ep⟩) "env" ({destination_name := "fwd1", content := c} : Message) (n+1)
    = cfgReturns (RRD q1 q2 4 ⟨eα,ep⟩) "fwd1" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RRD, realPinsFstD, realWires, Router.route, Pt1, Pt2, Forwarder, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelRD_4_fwd2 (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RRD q1 q2 4 ⟨eα,ep⟩) "env" ({destination_name := "fwd2", content := c} : Message) (n+1)
    = cfgReturns (RRD q1 q2 4 ⟨eα,ep⟩) "fwd2" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RRD, realPinsFstD, realWires, Router.route, Pt1, Pt2, Forwarder, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelRD_2_pt2 (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RRD q1 q2 2 ⟨eα,ep⟩) "env" ({destination_name := "pt2", content := c} : Message) (n+2)
    = cfgReturns (RRD q1 q2 3 ⟨eα,ep⟩) "fwd2"
        ({destination_name := "env",
          content := string2selfdelimitingString "pt2"
            ++ toString ({destination_name := "pt1", content := pwr "g" q2} : Message)} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RRD, realPinsFstD, realWires, Router.route, Pt1, Pt2, Forwarder, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, message_roundtrip, bind, PMF.pure_bind]

theorem peelRD_3_fwd2 (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RRD q1 q2 3 ⟨eα,ep⟩) "env" ({destination_name := "fwd2", content := c} : Message) (n+2)
    = cfgReturns (RRD q1 q2 4 ⟨eα,ep⟩) "pt1"
        ({destination_name := "env", content := pwr (pwr "g" q2) q1} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RRD, realPinsFstD, realWires, Router.route, Pt1, Pt2, Forwarder, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, message_roundtrip, bind, PMF.pure_bind]

theorem peelRD_other (i : ℕ) (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env")
    (md mc : String) (h1 : md ≠ "experiment") (h2 : md ≠ "pt1") (h3 : md ≠ "pt2")
    (h4 : md ≠ "fwd1") (h5 : md ≠ "fwd2") (h6 : md ≠ "env") (n : ℕ) :
    cfgReturns (RRD q1 q2 i ⟨eα,ep⟩) "env" ({destination_name := md, content := mc} : Message) (n+1)
    = cfgReturns (RRD q1 q2 i ⟨eα,ep⟩) "env"
        (destinationEnvMessage ({destination_name := md, content := mc} : Message)) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RRD, realPinsFstD, realWires, Router.route, Pt1, Pt2, Forwarder, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, h1, h2, h3, h4, h5, h6, Finset.mem_insert, Finset.mem_singleton, bind, PMF.pure_bind]


theorem funcIrrel_le (q1 q2 : Nat) : ∀ (k i : ℕ) (eα : Type) (ep : Pin eα) (s : String) (m : Message),
    ep.name = "env" → m.destination_name = "env" → sOK s → 2 ≤ i → i ≤ 4 →
    cfgReturns (RRD q1 q2 i ⟨eα,ep⟩) s m k ≤ ReturnsToExperiment (RRF q1 q2 i ⟨eα,ep⟩) s m := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i eα ep s m henv hm hs h2i hi
    cases k with
    | zero => rw [cfgReturns_zero_nexp _ _ _ (by rw [hm]; decide)]; exact zero_le
    | succ n =>
      rw [cfgReturns_env_deliver_gen _ _ _ (by rw [hm]; decide) (delivRealD q1 q2 i hi eα ep s m henv hm hs) n,
          ReturnsToExperiment_env_deliver_gen _ _ _ (by rw [hm]; decide) (delivReal q1 q2 i hi eα ep s m henv hm hs)]
      apply ENNReal.tsum_le_tsum
      intro x
      apply mul_le_mul_left'
      obtain ⟨⟨md, mc⟩, ns⟩ := x
      set ep2 := envStep ep ns with hep2
      have hname2 : ep2.name = "env" := by rw [hep2]; exact envStep_name ep ns henv
      rcases i with _|_|_|_|_|i
      · omega
      · omega
      · -- phase 2
        by_cases h_exp : md = "experiment"
        · subst h_exp
          rw [cfgReturns_exp _ _ _ rfl, ReturnsToExperiment_eq_iSup]
          exact le_iSup_of_le 0 (le_of_eq (cfgReturns_exp _ _ _ rfl 0).symm)
        by_cases h_env : md = "env"
        · subst h_env
          exact ih n (Nat.lt_succ_self n) 2 eα ep2 "env" ⟨"env", mc⟩ hname2 rfl sOK_env (by omega) (by omega)
        by_cases h_pt1 : md = "pt1"
        · subst h_pt1
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 1 n
            (peelRD_2_pt1 q1 q2 eα ep2 hname2 mc) (peelR_2_pt1 q1 q2 eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 2 eα ep2 "pt1" ⟨"env", contentError⟩ hname2 rfl sOK_pt1 (by omega) (by omega))
        by_cases h_pt2 : md = "pt2"
        · subst h_pt2
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 2 2 n
            (peelRD_2_pt2 q1 q2 eα ep2 hname2 mc) (peelR_2_pt2 q1 q2 eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 3 eα ep2 "fwd2" ⟨"env", string2selfdelimitingString "pt2" ++ toString ({destination_name := "pt1", content := pwr "g" q2} : Message)⟩ hname2 rfl sOK_fwd2 (by omega) (by omega))
        by_cases h_fwd1 : md = "fwd1"
        · subst h_fwd1
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 1 n
            (peelRD_2_fwd1 q1 q2 eα ep2 hname2 mc) (peelR_2_fwd1 q1 q2 eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 2 eα ep2 "fwd1" ⟨"env", contentError⟩ hname2 rfl sOK_fwd1 (by omega) (by omega))
        by_cases h_fwd2 : md = "fwd2"
        · subst h_fwd2
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 1 n
            (peelRD_2_fwd2 q1 q2 eα ep2 hname2 mc) (peelR_2_fwd2 q1 q2 eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 2 eα ep2 "fwd2" ⟨"env", contentError⟩ hname2 rfl sOK_fwd2 (by omega) (by omega))
        · exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 1 n
            (peelRD_other 2 q1 q2 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env) (peelR_other q1 q2 2 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env)
            (ih n (Nat.lt_succ_self n) 2 eα ep2 "env" (destinationEnvMessage ⟨md, mc⟩) hname2 (by simp [destinationEnvMessage]) sOK_env (by omega) (by omega))
      · -- phase 3
        by_cases h_exp : md = "experiment"
        · subst h_exp
          rw [cfgReturns_exp _ _ _ rfl, ReturnsToExperiment_eq_iSup]
          exact le_iSup_of_le 0 (le_of_eq (cfgReturns_exp _ _ _ rfl 0).symm)
        by_cases h_env : md = "env"
        · subst h_env
          exact ih n (Nat.lt_succ_self n) 3 eα ep2 "env" ⟨"env", mc⟩ hname2 rfl sOK_env (by omega) (by omega)
        by_cases h_pt1 : md = "pt1"
        · subst h_pt1
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 1 n
            (peelRD_3_pt1 q1 q2 eα ep2 hname2 mc) (peelR_3_pt1 q1 q2 eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 3 eα ep2 "pt1" ⟨"env", contentError⟩ hname2 rfl sOK_pt1 (by omega) (by omega))
        by_cases h_pt2 : md = "pt2"
        · subst h_pt2
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 1 n
            (peelRD_3_pt2 q1 q2 eα ep2 hname2 mc) (peelR_3_pt2 q1 q2 eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 3 eα ep2 "pt2" ⟨"env", contentError⟩ hname2 rfl sOK_pt2 (by omega) (by omega))
        by_cases h_fwd1 : md = "fwd1"
        · subst h_fwd1
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 1 n
            (peelRD_3_fwd1 q1 q2 eα ep2 hname2 mc) (peelR_3_fwd1 q1 q2 eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 3 eα ep2 "fwd1" ⟨"env", contentError⟩ hname2 rfl sOK_fwd1 (by omega) (by omega))
        by_cases h_fwd2 : md = "fwd2"
        · subst h_fwd2
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 2 2 n
            (peelRD_3_fwd2 q1 q2 eα ep2 hname2 mc) (peelR_3_fwd2 q1 q2 eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 4 eα ep2 "pt1" ⟨"env", pwr (pwr "g" q2) q1⟩ hname2 rfl sOK_pt1 (by omega) (by omega))
        · exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 1 n
            (peelRD_other 3 q1 q2 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env) (peelR_other q1 q2 3 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env)
            (ih n (Nat.lt_succ_self n) 3 eα ep2 "env" (destinationEnvMessage ⟨md, mc⟩) hname2 (by simp [destinationEnvMessage]) sOK_env (by omega) (by omega))
      · -- phase 4
        by_cases h_exp : md = "experiment"
        · subst h_exp
          rw [cfgReturns_exp _ _ _ rfl, ReturnsToExperiment_eq_iSup]
          exact le_iSup_of_le 0 (le_of_eq (cfgReturns_exp _ _ _ rfl 0).symm)
        by_cases h_env : md = "env"
        · subst h_env
          exact ih n (Nat.lt_succ_self n) 4 eα ep2 "env" ⟨"env", mc⟩ hname2 rfl sOK_env (by omega) (by omega)
        by_cases h_pt1 : md = "pt1"
        · subst h_pt1
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 1 n
            (peelRD_4_pt1 q1 q2 eα ep2 hname2 mc) (peelR_4_pt1 q1 q2 eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 4 eα ep2 "pt1" ⟨"env", contentError⟩ hname2 rfl sOK_pt1 (by omega) (by omega))
        by_cases h_pt2 : md = "pt2"
        · subst h_pt2
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 1 n
            (peelRD_4_pt2 q1 q2 eα ep2 hname2 mc) (peelR_4_pt2 q1 q2 eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 4 eα ep2 "pt2" ⟨"env", contentError⟩ hname2 rfl sOK_pt2 (by omega) (by omega))
        by_cases h_fwd1 : md = "fwd1"
        · subst h_fwd1
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 1 n
            (peelRD_4_fwd1 q1 q2 eα ep2 hname2 mc) (peelR_4_fwd1 q1 q2 eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 4 eα ep2 "fwd1" ⟨"env", contentError⟩ hname2 rfl sOK_fwd1 (by omega) (by omega))
        by_cases h_fwd2 : md = "fwd2"
        · subst h_fwd2
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 1 n
            (peelRD_4_fwd2 q1 q2 eα ep2 hname2 mc) (peelR_4_fwd2 q1 q2 eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 4 eα ep2 "fwd2" ⟨"env", contentError⟩ hname2 rfl sOK_fwd2 (by omega) (by omega))
        · exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 1 n
            (peelRD_other 4 q1 q2 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env) (peelR_other q1 q2 4 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env)
            (ih n (Nat.lt_succ_self n) 4 eα ep2 "env" (destinationEnvMessage ⟨md, mc⟩) hname2 (by simp [destinationEnvMessage]) sOK_env (by omega) (by omega))
      · exact absurd hi (by omega)

theorem funcIrrel_ge (q1 q2 : Nat) : ∀ (k i : ℕ) (eα : Type) (ep : Pin eα) (s : String) (m : Message),
    ep.name = "env" → m.destination_name = "env" → sOK s → 2 ≤ i → i ≤ 4 →
    cfgReturns (RRF q1 q2 i ⟨eα,ep⟩) s m k ≤ ReturnsToExperiment (RRD q1 q2 i ⟨eα,ep⟩) s m := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i eα ep s m henv hm hs h2i hi
    cases k with
    | zero => rw [cfgReturns_zero_nexp _ _ _ (by rw [hm]; decide)]; exact zero_le
    | succ n =>
      rw [cfgReturns_env_deliver_gen _ _ _ (by rw [hm]; decide) (delivReal q1 q2 i hi eα ep s m henv hm hs) n,
          ReturnsToExperiment_env_deliver_gen _ _ _ (by rw [hm]; decide) (delivRealD q1 q2 i hi eα ep s m henv hm hs)]
      apply ENNReal.tsum_le_tsum
      intro x
      apply mul_le_mul_left'
      obtain ⟨⟨md, mc⟩, ns⟩ := x
      set ep2 := envStep ep ns with hep2
      have hname2 : ep2.name = "env" := by rw [hep2]; exact envStep_name ep ns henv
      rcases i with _|_|_|_|_|i
      · omega
      · omega
      · -- phase 2
        by_cases h_exp : md = "experiment"
        · subst h_exp
          rw [cfgReturns_exp _ _ _ rfl, ReturnsToExperiment_eq_iSup]
          exact le_iSup_of_le 0 (le_of_eq (cfgReturns_exp _ _ _ rfl 0).symm)
        by_cases h_env : md = "env"
        · subst h_env
          exact ih n (Nat.lt_succ_self n) 2 eα ep2 "env" ⟨"env", mc⟩ hname2 rfl sOK_env (by omega) (by omega)
        by_cases h_pt1 : md = "pt1"
        · subst h_pt1
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 1 n
            (peelR_2_pt1 q1 q2 eα ep2 hname2 mc) (peelRD_2_pt1 q1 q2 eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 2 eα ep2 "pt1" ⟨"env", contentError⟩ hname2 rfl sOK_pt1 (by omega) (by omega))
        by_cases h_pt2 : md = "pt2"
        · subst h_pt2
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 2 2 n
            (peelR_2_pt2 q1 q2 eα ep2 hname2 mc) (peelRD_2_pt2 q1 q2 eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 3 eα ep2 "fwd2" ⟨"env", string2selfdelimitingString "pt2" ++ toString ({destination_name := "pt1", content := pwr "g" q2} : Message)⟩ hname2 rfl sOK_fwd2 (by omega) (by omega))
        by_cases h_fwd1 : md = "fwd1"
        · subst h_fwd1
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 1 n
            (peelR_2_fwd1 q1 q2 eα ep2 hname2 mc) (peelRD_2_fwd1 q1 q2 eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 2 eα ep2 "fwd1" ⟨"env", contentError⟩ hname2 rfl sOK_fwd1 (by omega) (by omega))
        by_cases h_fwd2 : md = "fwd2"
        · subst h_fwd2
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 1 n
            (peelR_2_fwd2 q1 q2 eα ep2 hname2 mc) (peelRD_2_fwd2 q1 q2 eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 2 eα ep2 "fwd2" ⟨"env", contentError⟩ hname2 rfl sOK_fwd2 (by omega) (by omega))
        · exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 1 n
            (peelR_other q1 q2 2 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env) (peelRD_other 2 q1 q2 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env)
            (ih n (Nat.lt_succ_self n) 2 eα ep2 "env" (destinationEnvMessage ⟨md, mc⟩) hname2 (by simp [destinationEnvMessage]) sOK_env (by omega) (by omega))
      · -- phase 3
        by_cases h_exp : md = "experiment"
        · subst h_exp
          rw [cfgReturns_exp _ _ _ rfl, ReturnsToExperiment_eq_iSup]
          exact le_iSup_of_le 0 (le_of_eq (cfgReturns_exp _ _ _ rfl 0).symm)
        by_cases h_env : md = "env"
        · subst h_env
          exact ih n (Nat.lt_succ_self n) 3 eα ep2 "env" ⟨"env", mc⟩ hname2 rfl sOK_env (by omega) (by omega)
        by_cases h_pt1 : md = "pt1"
        · subst h_pt1
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 1 n
            (peelR_3_pt1 q1 q2 eα ep2 hname2 mc) (peelRD_3_pt1 q1 q2 eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 3 eα ep2 "pt1" ⟨"env", contentError⟩ hname2 rfl sOK_pt1 (by omega) (by omega))
        by_cases h_pt2 : md = "pt2"
        · subst h_pt2
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 1 n
            (peelR_3_pt2 q1 q2 eα ep2 hname2 mc) (peelRD_3_pt2 q1 q2 eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 3 eα ep2 "pt2" ⟨"env", contentError⟩ hname2 rfl sOK_pt2 (by omega) (by omega))
        by_cases h_fwd1 : md = "fwd1"
        · subst h_fwd1
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 1 n
            (peelR_3_fwd1 q1 q2 eα ep2 hname2 mc) (peelRD_3_fwd1 q1 q2 eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 3 eα ep2 "fwd1" ⟨"env", contentError⟩ hname2 rfl sOK_fwd1 (by omega) (by omega))
        by_cases h_fwd2 : md = "fwd2"
        · subst h_fwd2
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 2 2 n
            (peelR_3_fwd2 q1 q2 eα ep2 hname2 mc) (peelRD_3_fwd2 q1 q2 eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 4 eα ep2 "pt1" ⟨"env", pwr (pwr "g" q2) q1⟩ hname2 rfl sOK_pt1 (by omega) (by omega))
        · exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 1 n
            (peelR_other q1 q2 3 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env) (peelRD_other 3 q1 q2 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env)
            (ih n (Nat.lt_succ_self n) 3 eα ep2 "env" (destinationEnvMessage ⟨md, mc⟩) hname2 (by simp [destinationEnvMessage]) sOK_env (by omega) (by omega))
      · -- phase 4
        by_cases h_exp : md = "experiment"
        · subst h_exp
          rw [cfgReturns_exp _ _ _ rfl, ReturnsToExperiment_eq_iSup]
          exact le_iSup_of_le 0 (le_of_eq (cfgReturns_exp _ _ _ rfl 0).symm)
        by_cases h_env : md = "env"
        · subst h_env
          exact ih n (Nat.lt_succ_self n) 4 eα ep2 "env" ⟨"env", mc⟩ hname2 rfl sOK_env (by omega) (by omega)
        by_cases h_pt1 : md = "pt1"
        · subst h_pt1
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 1 n
            (peelR_4_pt1 q1 q2 eα ep2 hname2 mc) (peelRD_4_pt1 q1 q2 eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 4 eα ep2 "pt1" ⟨"env", contentError⟩ hname2 rfl sOK_pt1 (by omega) (by omega))
        by_cases h_pt2 : md = "pt2"
        · subst h_pt2
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 1 n
            (peelR_4_pt2 q1 q2 eα ep2 hname2 mc) (peelRD_4_pt2 q1 q2 eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 4 eα ep2 "pt2" ⟨"env", contentError⟩ hname2 rfl sOK_pt2 (by omega) (by omega))
        by_cases h_fwd1 : md = "fwd1"
        · subst h_fwd1
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 1 n
            (peelR_4_fwd1 q1 q2 eα ep2 hname2 mc) (peelRD_4_fwd1 q1 q2 eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 4 eα ep2 "fwd1" ⟨"env", contentError⟩ hname2 rfl sOK_fwd1 (by omega) (by omega))
        by_cases h_fwd2 : md = "fwd2"
        · subst h_fwd2
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 1 n
            (peelR_4_fwd2 q1 q2 eα ep2 hname2 mc) (peelRD_4_fwd2 q1 q2 eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 4 eα ep2 "fwd2" ⟨"env", contentError⟩ hname2 rfl sOK_fwd2 (by omega) (by omega))
        · exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 1 n
            (peelR_other q1 q2 4 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env) (peelRD_other 4 q1 q2 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env)
            (ih n (Nat.lt_succ_self n) 4 eα ep2 "env" (destinationEnvMessage ⟨md, mc⟩) hname2 (by simp [destinationEnvMessage]) sOK_env (by omega) (by omega))
      · exact absurd hi (by omega)

theorem funcIrrel_RTE (q1 q2 : Nat) (i : ℕ) (eα : Type) (ep : Pin eα) (s : String) (m : Message)
    (henv : ep.name = "env") (hm : m.destination_name = "env") (hs : sOK s) (h2i : 2 ≤ i) (hi : i ≤ 4) :
    ReturnsToExperiment (RRD q1 q2 i ⟨eα,ep⟩) s m = ReturnsToExperiment (RRF q1 q2 i ⟨eα,ep⟩) s m := by
  apply le_antisymm
  · rw [ReturnsToExperiment_eq_iSup (RRD q1 q2 i ⟨eα,ep⟩)]
    exact iSup_le (fun k => funcIrrel_le q1 q2 k i eα ep s m henv hm hs h2i hi)
  · rw [ReturnsToExperiment_eq_iSup (RRF q1 q2 i ⟨eα,ep⟩)]
    exact iSup_le (fun k => funcIrrel_ge q1 q2 k i eα ep s m henv hm hs h2i hi)

-- Draw peels: Pt1 draws q1 at phase 0; Pt2 draws q2 at phase 1.
theorem peelRD_0_pt1 (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RRD q1 q2 0 ⟨eα,ep⟩) "env" ({destination_name := "pt1", content := c} : Message) (n+2)
    = ∑' q, rnd q * cfgReturns (RRD q q2 1 ⟨eα,ep⟩) "fwd1"
        ({destination_name := "env",
          content := string2selfdelimitingString "pt1"
            ++ toString ({destination_name := "pt2", content := pwr "g" q} : Message)} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RRD, realPinsFstD, realWires, Router.route,
    Pt1, Pt2, Forwarder, Pin.invoke, changePinOfName, Machine.errorMessage2sender,
    List.find?, List.map, henv, message_roundtrip, bind, PMF.pure_bind, PMF.bind_apply]

theorem peelRD_1_fwd1 (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RRD q1 q2 1 ⟨eα,ep⟩) "env" ({destination_name := "fwd1", content := c} : Message) (n+2)
    = ∑' q, rnd q * cfgReturns (RRD q1 q 2 ⟨eα,ep⟩) "pt2"
        ({destination_name := "env", content := pwr (pwr "g" q1) q} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RRD, realPinsFstD, realWires, Router.route,
    Pt1, Pt2, Forwarder, Pin.invoke, changePinOfName, Machine.errorMessage2sender,
    List.find?, List.map, henv, message_roundtrip, bind, PMF.pure_bind, PMF.bind_apply]

-- RTE-level RRD peels (from the cfgReturns D-peels).
theorem RTE_RRD_1_fwd1 (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) :
    ReturnsToExperiment (RRD q1 q2 1 ⟨eα,ep⟩) "env" ({destination_name := "fwd1", content := c} : Message)
    = ∑' q, rnd q * ReturnsToExperiment (RRD q1 q 2 ⟨eα,ep⟩) "pt2"
        ({destination_name := "env", content := pwr (pwr "g" q1) q} : Message) := by
  rw [ReturnsToExperiment_eq_iSup, ← iSup_cfgReturns_shift _ _ _ 2]
  simp_rw [peelRD_1_fwd1 q1 q2 eα ep henv c]
  rw [(tsum_mul_iSup_comm rnd
      (fun n q => cfgReturns (RRD q1 q 2 ⟨eα,ep⟩) "pt2" ({destination_name := "env", content := pwr (pwr "g" q1) q} : Message) n)
      (fun q => cfgReturns_monotone _ _ _)).symm]
  simp_rw [← ReturnsToExperiment_eq_iSup]

theorem RTE_RRD_0_pt1 (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) :
    ReturnsToExperiment (RRD q1 q2 0 ⟨eα,ep⟩) "env" ({destination_name := "pt1", content := c} : Message)
    = ∑' q, rnd q * ReturnsToExperiment (RRD q q2 1 ⟨eα,ep⟩) "fwd1"
        ({destination_name := "env",
          content := string2selfdelimitingString "pt1"
            ++ toString ({destination_name := "pt2", content := pwr "g" q} : Message)} : Message) := by
  rw [ReturnsToExperiment_eq_iSup, ← iSup_cfgReturns_shift _ _ _ 2]
  simp_rw [peelRD_0_pt1 q1 q2 eα ep henv c]
  rw [(tsum_mul_iSup_comm rnd
      (fun n q => cfgReturns (RRD q q2 1 ⟨eα,ep⟩) "fwd1" ({destination_name := "env", content := string2selfdelimitingString "pt1" ++ toString ({destination_name := "pt2", content := pwr "g" q} : Message)} : Message) n)
      (fun q => cfgReturns_monotone _ _ _)).symm]
  simp_rw [← ReturnsToExperiment_eq_iSup]

theorem tsum_swap_mul {A B : Type*} (D : A → ENNReal) (r : B → ENNReal) (f : B → A → ENNReal) :
    ∑' b, r b * ∑' a, D a * f b a = ∑' a, D a * ∑' b, r b * f b a := by
  have e1 : (∑' b, r b * ∑' a, D a * f b a) = ∑' b, ∑' a, r b * (D a * f b a) :=
    tsum_congr (fun b => (ENNReal.tsum_mul_left).symm)
  have e2 : (∑' a, D a * ∑' b, r b * f b a) = ∑' a, ∑' b, D a * (r b * f b a) :=
    tsum_congr (fun a => (ENNReal.tsum_mul_left).symm)
  rw [e1, e2, ENNReal.tsum_comm]
  refine tsum_congr (fun a => tsum_congr (fun b => ?_)); ring

-- pull_ge at phase 1: factor Pt2's coin.
theorem pull_ge_1 (q1 : Nat) : ∀ (k : ℕ) (q2 : Nat) (eα : Type) (ep : Pin eα) (s : String) (m : Message),
    ep.name = "env" → m.destination_name = "env" → sOK s →
    ∑' b, rnd b * cfgReturns (RRF q1 b 1 ⟨eα,ep⟩) s m k ≤ ReturnsToExperiment (RRD q1 q2 1 ⟨eα,ep⟩) s m := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro q2 eα ep s m henv hm hs
    cases k with
    | zero =>
      have : ∀ b, cfgReturns (RRF q1 b 1 ⟨eα,ep⟩) s m 0 = 0 :=
        fun b => cfgReturns_zero_nexp _ _ _ (by rw [hm]; decide)
      simp [this]
    | succ n =>
      rw [ReturnsToExperiment_env_deliver_gen _ _ _ (by rw [hm]; decide) (delivRealD q1 q2 1 (by omega) eα ep s m henv hm hs)]
      have hstep : ∀ b, cfgReturns (RRF q1 b 1 ⟨eα,ep⟩) s m (n+1)
          = ∑' x, (ep.machine.func s m ep.machine.state) x
              * cfgReturns (RRF q1 b 1 ⟨eα, envStep ep x.2⟩) "env" x.1 n :=
        fun b => cfgReturns_env_deliver_gen _ _ _ (by rw [hm]; decide) (delivReal q1 b 1 (by omega) eα ep s m henv hm hs) n
      simp_rw [hstep]
      rw [tsum_swap_mul]
      apply ENNReal.tsum_le_tsum
      intro x
      apply mul_le_mul_left'
      obtain ⟨⟨md, mc⟩, ns⟩ := x
      set ep2 := envStep ep ns with hep2
      have hname2 : ep2.name = "env" := by rw [hep2]; exact envStep_name ep ns henv
      by_cases h_exp : md = "experiment"
      · subst h_exp
        have h1 : ∀ b, cfgReturns (RRF q1 b 1 ⟨eα,ep2⟩) "env" ⟨"experiment", mc⟩ n = 1 :=
          fun b => cfgReturns_exp _ _ _ rfl n
        simp_rw [h1]
        rw [ENNReal.tsum_mul_right, rnd.tsum_coe, one_mul]
        rw [ReturnsToExperiment_eq_iSup]
        exact le_iSup_of_le 0 (le_of_eq (cfgReturns_exp _ _ _ rfl 0).symm)
      by_cases h_env : md = "env"
      · subst h_env
        exact ih n (Nat.lt_succ_self n) q2 eα ep2 "env" ⟨"env", mc⟩ hname2 rfl sOK_env
      by_cases h_pt1 : md = "pt1"
      · subst h_pt1
        calc ∑' b, rnd b * cfgReturns (RRF q1 b 1 ⟨eα,ep2⟩) "env" ⟨"pt1", mc⟩ n
            ≤ ∑' b, rnd b * cfgReturns (RRF q1 b 1 ⟨eα,ep2⟩) "pt1" ⟨"env", contentError⟩ n := by
              apply ENNReal.tsum_le_tsum; intro b; apply mul_le_mul_left'
              calc cfgReturns (RRF q1 b 1 ⟨eα,ep2⟩) "env" ⟨"pt1", mc⟩ n
                  ≤ cfgReturns (RRF q1 b 1 ⟨eα,ep2⟩) "env" ⟨"pt1", mc⟩ (n+1) := cfgReturns_le_add _ _ _ _ _
                _ = cfgReturns (RRF q1 b 1 ⟨eα,ep2⟩) "pt1" ⟨"env", contentError⟩ n := peelR_1_pt1 q1 b eα ep2 hname2 mc n
          _ ≤ ReturnsToExperiment (RRD q1 q2 1 ⟨eα,ep2⟩) "pt1" ⟨"env", contentError⟩ :=
              ih n (Nat.lt_succ_self n) q2 eα ep2 "pt1" ⟨"env", contentError⟩ hname2 rfl sOK_pt1
          _ = ReturnsToExperiment (RRD q1 q2 1 ⟨eα,ep2⟩) "env" ⟨"pt1", mc⟩ :=
              (ReturnsToExperiment_of_peel 1 (peelRD_1_pt1 q1 q2 eα ep2 hname2 mc)).symm
      by_cases h_pt2 : md = "pt2"
      · subst h_pt2
        calc ∑' b, rnd b * cfgReturns (RRF q1 b 1 ⟨eα,ep2⟩) "env" ⟨"pt2", mc⟩ n
            ≤ ∑' b, rnd b * cfgReturns (RRF q1 b 1 ⟨eα,ep2⟩) "pt2" ⟨"env", contentError⟩ n := by
              apply ENNReal.tsum_le_tsum; intro b; apply mul_le_mul_left'
              calc cfgReturns (RRF q1 b 1 ⟨eα,ep2⟩) "env" ⟨"pt2", mc⟩ n
                  ≤ cfgReturns (RRF q1 b 1 ⟨eα,ep2⟩) "env" ⟨"pt2", mc⟩ (n+1) := cfgReturns_le_add _ _ _ _ _
                _ = cfgReturns (RRF q1 b 1 ⟨eα,ep2⟩) "pt2" ⟨"env", contentError⟩ n := peelR_1_pt2 q1 b eα ep2 hname2 mc n
          _ ≤ ReturnsToExperiment (RRD q1 q2 1 ⟨eα,ep2⟩) "pt2" ⟨"env", contentError⟩ :=
              ih n (Nat.lt_succ_self n) q2 eα ep2 "pt2" ⟨"env", contentError⟩ hname2 rfl sOK_pt2
          _ = ReturnsToExperiment (RRD q1 q2 1 ⟨eα,ep2⟩) "env" ⟨"pt2", mc⟩ :=
              (ReturnsToExperiment_of_peel 1 (peelRD_1_pt2 q1 q2 eα ep2 hname2 mc)).symm
      by_cases h_fwd1 : md = "fwd1"
      · subst h_fwd1
        calc ∑' b, rnd b * cfgReturns (RRF q1 b 1 ⟨eα,ep2⟩) "env" ⟨"fwd1", mc⟩ n
            ≤ ∑' b, rnd b * cfgReturns (RRF q1 b 2 ⟨eα,ep2⟩) "pt2" ⟨"env", pwr (pwr "g" q1) b⟩ n := by
              apply ENNReal.tsum_le_tsum; intro b; apply mul_le_mul_left'
              calc cfgReturns (RRF q1 b 1 ⟨eα,ep2⟩) "env" ⟨"fwd1", mc⟩ n
                  ≤ cfgReturns (RRF q1 b 1 ⟨eα,ep2⟩) "env" ⟨"fwd1", mc⟩ (n+2) := cfgReturns_le_add _ _ _ _ _
                _ = cfgReturns (RRF q1 b 2 ⟨eα,ep2⟩) "pt2" ⟨"env", pwr (pwr "g" q1) b⟩ n := peelR_1_fwd1 q1 b eα ep2 hname2 mc n
          _ ≤ ∑' b, rnd b * ReturnsToExperiment (RRD q1 b 2 ⟨eα,ep2⟩) "pt2" ⟨"env", pwr (pwr "g" q1) b⟩ := by
              apply ENNReal.tsum_le_tsum; intro b; apply mul_le_mul_left'
              calc cfgReturns (RRF q1 b 2 ⟨eα,ep2⟩) "pt2" ⟨"env", pwr (pwr "g" q1) b⟩ n
                  ≤ ReturnsToExperiment (RRF q1 b 2 ⟨eα,ep2⟩) "pt2" ⟨"env", pwr (pwr "g" q1) b⟩ :=
                    le_iSup (fun j => cfgReturns (RRF q1 b 2 ⟨eα,ep2⟩) "pt2" ⟨"env", pwr (pwr "g" q1) b⟩ j) n
                _ = ReturnsToExperiment (RRD q1 b 2 ⟨eα,ep2⟩) "pt2" ⟨"env", pwr (pwr "g" q1) b⟩ :=
                    (funcIrrel_RTE q1 b 2 eα ep2 "pt2" ⟨"env", pwr (pwr "g" q1) b⟩ hname2 rfl sOK_pt2 (by omega) (by omega)).symm
          _ = ReturnsToExperiment (RRD q1 q2 1 ⟨eα,ep2⟩) "env" ⟨"fwd1", mc⟩ :=
              (RTE_RRD_1_fwd1 q1 q2 eα ep2 hname2 mc).symm
      by_cases h_fwd2 : md = "fwd2"
      · subst h_fwd2
        calc ∑' b, rnd b * cfgReturns (RRF q1 b 1 ⟨eα,ep2⟩) "env" ⟨"fwd2", mc⟩ n
            ≤ ∑' b, rnd b * cfgReturns (RRF q1 b 1 ⟨eα,ep2⟩) "fwd2" ⟨"env", contentError⟩ n := by
              apply ENNReal.tsum_le_tsum; intro b; apply mul_le_mul_left'
              calc cfgReturns (RRF q1 b 1 ⟨eα,ep2⟩) "env" ⟨"fwd2", mc⟩ n
                  ≤ cfgReturns (RRF q1 b 1 ⟨eα,ep2⟩) "env" ⟨"fwd2", mc⟩ (n+1) := cfgReturns_le_add _ _ _ _ _
                _ = cfgReturns (RRF q1 b 1 ⟨eα,ep2⟩) "fwd2" ⟨"env", contentError⟩ n := peelR_1_fwd2 q1 b eα ep2 hname2 mc n
          _ ≤ ReturnsToExperiment (RRD q1 q2 1 ⟨eα,ep2⟩) "fwd2" ⟨"env", contentError⟩ :=
              ih n (Nat.lt_succ_self n) q2 eα ep2 "fwd2" ⟨"env", contentError⟩ hname2 rfl sOK_fwd2
          _ = ReturnsToExperiment (RRD q1 q2 1 ⟨eα,ep2⟩) "env" ⟨"fwd2", mc⟩ :=
              (ReturnsToExperiment_of_peel 1 (peelRD_1_fwd2 q1 q2 eα ep2 hname2 mc)).symm
      · calc ∑' b, rnd b * cfgReturns (RRF q1 b 1 ⟨eα,ep2⟩) "env" ⟨md, mc⟩ n
            ≤ ∑' b, rnd b * cfgReturns (RRF q1 b 1 ⟨eα,ep2⟩) "env" (destinationEnvMessage ⟨md, mc⟩) n := by
              apply ENNReal.tsum_le_tsum; intro b; apply mul_le_mul_left'
              calc cfgReturns (RRF q1 b 1 ⟨eα,ep2⟩) "env" ⟨md, mc⟩ n
                  ≤ cfgReturns (RRF q1 b 1 ⟨eα,ep2⟩) "env" ⟨md, mc⟩ (n+1) := cfgReturns_le_add _ _ _ _ _
                _ = cfgReturns (RRF q1 b 1 ⟨eα,ep2⟩) "env" (destinationEnvMessage ⟨md, mc⟩) n := peelR_other q1 b 1 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env n
          _ ≤ ReturnsToExperiment (RRD q1 q2 1 ⟨eα,ep2⟩) "env" (destinationEnvMessage ⟨md, mc⟩) :=
              ih n (Nat.lt_succ_self n) q2 eα ep2 "env" (destinationEnvMessage ⟨md, mc⟩) hname2 (by simp [destinationEnvMessage]) sOK_env
          _ = ReturnsToExperiment (RRD q1 q2 1 ⟨eα,ep2⟩) "env" ⟨md, mc⟩ :=
              (ReturnsToExperiment_of_peel 1 (peelRD_other 1 q1 q2 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env)).symm

-- pull_ge at phase 0: factor Pt1's coin, then delegate to pull_ge_1.
theorem pull_ge_0 : ∀ (k : ℕ) (q1 q2 : Nat) (eα : Type) (ep : Pin eα) (s : String) (m : Message),
    ep.name = "env" → m.destination_name = "env" → sOK s →
    ∑' a, rnd a * ∑' b, rnd b * cfgReturns (RRF a b 0 ⟨eα,ep⟩) s m k
      ≤ ReturnsToExperiment (RRD q1 q2 0 ⟨eα,ep⟩) s m := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro q1 q2 eα ep s m henv hm hs
    cases k with
    | zero =>
      have : ∀ a b, cfgReturns (RRF a b 0 ⟨eα,ep⟩) s m 0 = 0 :=
        fun a b => cfgReturns_zero_nexp _ _ _ (by rw [hm]; decide)
      simp [this]
    | succ n =>
      rw [ReturnsToExperiment_env_deliver_gen _ _ _ (by rw [hm]; decide) (delivRealD q1 q2 0 (by omega) eα ep s m henv hm hs)]
      have hstep : ∀ a b, cfgReturns (RRF a b 0 ⟨eα,ep⟩) s m (n+1)
          = ∑' x, (ep.machine.func s m ep.machine.state) x
              * cfgReturns (RRF a b 0 ⟨eα, envStep ep x.2⟩) "env" x.1 n :=
        fun a b => cfgReturns_env_deliver_gen _ _ _ (by rw [hm]; decide) (delivReal a b 0 (by omega) eα ep s m henv hm hs) n
      simp_rw [hstep]
      rw [tsum_congr (fun a => congrArg (fun t => rnd a * t)
        (tsum_swap_mul (ep.machine.func s m ep.machine.state) rnd
          (fun b x => cfgReturns (RRF a b 0 ⟨eα, envStep ep x.2⟩) "env" x.1 n)))]
      rw [tsum_swap_mul (ep.machine.func s m ep.machine.state) rnd
        (fun a x => ∑' b, rnd b * cfgReturns (RRF a b 0 ⟨eα, envStep ep x.2⟩) "env" x.1 n)]
      apply ENNReal.tsum_le_tsum
      intro x
      apply mul_le_mul_left'
      obtain ⟨⟨md, mc⟩, ns⟩ := x
      set ep2 := envStep ep ns with hep2
      have hname2 : ep2.name = "env" := by rw [hep2]; exact envStep_name ep ns henv
      by_cases h_exp : md = "experiment"
      · subst h_exp
        have h1 : ∀ a b, cfgReturns (RRF a b 0 ⟨eα,ep2⟩) "env" ⟨"experiment", mc⟩ n = 1 :=
          fun a b => cfgReturns_exp _ _ _ rfl n
        have hR : ReturnsToExperiment (RRD q1 q2 0 ⟨eα,ep2⟩) "env" ⟨"experiment", mc⟩ = 1 := by
          rw [ReturnsToExperiment_eq_iSup]
          exact le_antisymm (iSup_le (fun k => le_of_eq (cfgReturns_exp _ _ _ rfl k)))
            (le_iSup_of_le 0 (le_of_eq (cfgReturns_exp _ _ _ rfl 0).symm))
        rw [hR]
        simp [h1, rnd.tsum_coe]
      by_cases h_env : md = "env"
      · subst h_env
        exact ih n (Nat.lt_succ_self n) q1 q2 eα ep2 "env" ⟨"env", mc⟩ hname2 rfl sOK_env
      by_cases h_pt1 : md = "pt1"
      · subst h_pt1
        calc ∑' a, rnd a * ∑' b, rnd b * cfgReturns (RRF a b 0 ⟨eα,ep2⟩) "env" ⟨"pt1", mc⟩ n
            ≤ ∑' a, rnd a * ∑' b, rnd b * cfgReturns (RRF a b 1 ⟨eα,ep2⟩) "fwd1"
                ⟨"env", string2selfdelimitingString "pt1" ++ toString ({destination_name := "pt2", content := pwr "g" a} : Message)⟩ n := by
              apply ENNReal.tsum_le_tsum; intro a; apply mul_le_mul_left'
              apply ENNReal.tsum_le_tsum; intro b; apply mul_le_mul_left'
              calc cfgReturns (RRF a b 0 ⟨eα,ep2⟩) "env" ⟨"pt1", mc⟩ n
                  ≤ cfgReturns (RRF a b 0 ⟨eα,ep2⟩) "env" ⟨"pt1", mc⟩ (n+2) := cfgReturns_le_add _ _ _ _ _
                _ = cfgReturns (RRF a b 1 ⟨eα,ep2⟩) "fwd1" ⟨"env", string2selfdelimitingString "pt1" ++ toString ({destination_name := "pt2", content := pwr "g" a} : Message)⟩ n := peelR_0_pt1 a b eα ep2 hname2 mc n
          _ ≤ ∑' a, rnd a * ReturnsToExperiment (RRD a q2 1 ⟨eα,ep2⟩) "fwd1"
                ⟨"env", string2selfdelimitingString "pt1" ++ toString ({destination_name := "pt2", content := pwr "g" a} : Message)⟩ := by
              apply ENNReal.tsum_le_tsum; intro a; apply mul_le_mul_left'
              exact pull_ge_1 a n q2 eα ep2 "fwd1" ⟨"env", string2selfdelimitingString "pt1" ++ toString ({destination_name := "pt2", content := pwr "g" a} : Message)⟩ hname2 rfl sOK_fwd1
          _ = ReturnsToExperiment (RRD q1 q2 0 ⟨eα,ep2⟩) "env" ⟨"pt1", mc⟩ := (RTE_RRD_0_pt1 q1 q2 eα ep2 hname2 mc).symm
      by_cases h_pt2 : md = "pt2"
      · subst h_pt2
        calc ∑' a, rnd a * ∑' b, rnd b * cfgReturns (RRF a b 0 ⟨eα,ep2⟩) "env" ⟨"pt2", mc⟩ n
            ≤ ∑' a, rnd a * ∑' b, rnd b * cfgReturns (RRF a b 0 ⟨eα,ep2⟩) "pt2" ⟨"env", contentError⟩ n := by
              apply ENNReal.tsum_le_tsum; intro a; apply mul_le_mul_left'
              apply ENNReal.tsum_le_tsum; intro b; apply mul_le_mul_left'
              calc cfgReturns (RRF a b 0 ⟨eα,ep2⟩) "env" ⟨"pt2", mc⟩ n
                  ≤ cfgReturns (RRF a b 0 ⟨eα,ep2⟩) "env" ⟨"pt2", mc⟩ (n+1) := cfgReturns_le_add _ _ _ _ _
                _ = cfgReturns (RRF a b 0 ⟨eα,ep2⟩) "pt2" ⟨"env", contentError⟩ n := peelR_0_pt2 a b eα ep2 hname2 mc n
          _ ≤ ReturnsToExperiment (RRD q1 q2 0 ⟨eα,ep2⟩) "pt2" ⟨"env", contentError⟩ :=
              ih n (Nat.lt_succ_self n) q1 q2 eα ep2 "pt2" ⟨"env", contentError⟩ hname2 rfl sOK_pt2
          _ = ReturnsToExperiment (RRD q1 q2 0 ⟨eα,ep2⟩) "env" ⟨"pt2", mc⟩ :=
              (ReturnsToExperiment_of_peel 1 (peelRD_0_pt2 q1 q2 eα ep2 hname2 mc)).symm
      by_cases h_fwd1 : md = "fwd1"
      · subst h_fwd1
        calc ∑' a, rnd a * ∑' b, rnd b * cfgReturns (RRF a b 0 ⟨eα,ep2⟩) "env" ⟨"fwd1", mc⟩ n
            ≤ ∑' a, rnd a * ∑' b, rnd b * cfgReturns (RRF a b 0 ⟨eα,ep2⟩) "fwd1" ⟨"env", contentError⟩ n := by
              apply ENNReal.tsum_le_tsum; intro a; apply mul_le_mul_left'
              apply ENNReal.tsum_le_tsum; intro b; apply mul_le_mul_left'
              calc cfgReturns (RRF a b 0 ⟨eα,ep2⟩) "env" ⟨"fwd1", mc⟩ n
                  ≤ cfgReturns (RRF a b 0 ⟨eα,ep2⟩) "env" ⟨"fwd1", mc⟩ (n+1) := cfgReturns_le_add _ _ _ _ _
                _ = cfgReturns (RRF a b 0 ⟨eα,ep2⟩) "fwd1" ⟨"env", contentError⟩ n := peelR_0_fwd1 a b eα ep2 hname2 mc n
          _ ≤ ReturnsToExperiment (RRD q1 q2 0 ⟨eα,ep2⟩) "fwd1" ⟨"env", contentError⟩ :=
              ih n (Nat.lt_succ_self n) q1 q2 eα ep2 "fwd1" ⟨"env", contentError⟩ hname2 rfl sOK_fwd1
          _ = ReturnsToExperiment (RRD q1 q2 0 ⟨eα,ep2⟩) "env" ⟨"fwd1", mc⟩ :=
              (ReturnsToExperiment_of_peel 1 (peelRD_0_fwd1 q1 q2 eα ep2 hname2 mc)).symm
      by_cases h_fwd2 : md = "fwd2"
      · subst h_fwd2
        calc ∑' a, rnd a * ∑' b, rnd b * cfgReturns (RRF a b 0 ⟨eα,ep2⟩) "env" ⟨"fwd2", mc⟩ n
            ≤ ∑' a, rnd a * ∑' b, rnd b * cfgReturns (RRF a b 0 ⟨eα,ep2⟩) "fwd2" ⟨"env", contentError⟩ n := by
              apply ENNReal.tsum_le_tsum; intro a; apply mul_le_mul_left'
              apply ENNReal.tsum_le_tsum; intro b; apply mul_le_mul_left'
              calc cfgReturns (RRF a b 0 ⟨eα,ep2⟩) "env" ⟨"fwd2", mc⟩ n
                  ≤ cfgReturns (RRF a b 0 ⟨eα,ep2⟩) "env" ⟨"fwd2", mc⟩ (n+1) := cfgReturns_le_add _ _ _ _ _
                _ = cfgReturns (RRF a b 0 ⟨eα,ep2⟩) "fwd2" ⟨"env", contentError⟩ n := peelR_0_fwd2 a b eα ep2 hname2 mc n
          _ ≤ ReturnsToExperiment (RRD q1 q2 0 ⟨eα,ep2⟩) "fwd2" ⟨"env", contentError⟩ :=
              ih n (Nat.lt_succ_self n) q1 q2 eα ep2 "fwd2" ⟨"env", contentError⟩ hname2 rfl sOK_fwd2
          _ = ReturnsToExperiment (RRD q1 q2 0 ⟨eα,ep2⟩) "env" ⟨"fwd2", mc⟩ :=
              (ReturnsToExperiment_of_peel 1 (peelRD_0_fwd2 q1 q2 eα ep2 hname2 mc)).symm
      · calc ∑' a, rnd a * ∑' b, rnd b * cfgReturns (RRF a b 0 ⟨eα,ep2⟩) "env" ⟨md, mc⟩ n
            ≤ ∑' a, rnd a * ∑' b, rnd b * cfgReturns (RRF a b 0 ⟨eα,ep2⟩) "env" (destinationEnvMessage ⟨md, mc⟩) n := by
              apply ENNReal.tsum_le_tsum; intro a; apply mul_le_mul_left'
              apply ENNReal.tsum_le_tsum; intro b; apply mul_le_mul_left'
              calc cfgReturns (RRF a b 0 ⟨eα,ep2⟩) "env" ⟨md, mc⟩ n
                  ≤ cfgReturns (RRF a b 0 ⟨eα,ep2⟩) "env" ⟨md, mc⟩ (n+1) := cfgReturns_le_add _ _ _ _ _
                _ = cfgReturns (RRF a b 0 ⟨eα,ep2⟩) "env" (destinationEnvMessage ⟨md, mc⟩) n := peelR_other a b 0 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env n
          _ ≤ ReturnsToExperiment (RRD q1 q2 0 ⟨eα,ep2⟩) "env" (destinationEnvMessage ⟨md, mc⟩) :=
              ih n (Nat.lt_succ_self n) q1 q2 eα ep2 "env" (destinationEnvMessage ⟨md, mc⟩) hname2 (by simp [destinationEnvMessage]) sOK_env
          _ = ReturnsToExperiment (RRD q1 q2 0 ⟨eα,ep2⟩) "env" ⟨md, mc⟩ :=
              (ReturnsToExperiment_of_peel 1 (peelRD_other 0 q1 q2 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env)).symm

-- Real pull-out (one direction, as needed for decompR).
theorem realPullout_ge (env : SPin) :
    ∑' q1, rnd q1 * ∑' q2, rnd q2 * detReal env q1 q2 ≤ experimentReal env := by
  obtain ⟨eα, ep⟩ := env
  by_cases hn : ep.name = "env"
  · show ∑' q1, rnd q1 * ∑' q2, rnd q2
          * ReturnsToExperiment (RRF q1 q2 0 ⟨eα,ep⟩) "experiment" startMessage
        ≤ ReturnsToExperiment (RRD 0 0 0 ⟨eα,ep⟩) "experiment" startMessage
    have hmono : ∀ q1, Monotone (fun k => ∑' q2, rnd q2 * cfgReturns (RRF q1 q2 0 ⟨eα,ep⟩) "experiment" startMessage k) := by
      intro q1 i j hij
      apply ENNReal.tsum_le_tsum; intro q2; exact mul_le_mul_left' (cfgReturns_monotone _ _ _ hij) _
    have hcomm : (∑' q1, rnd q1 * ∑' q2, rnd q2 * ReturnsToExperiment (RRF q1 q2 0 ⟨eα,ep⟩) "experiment" startMessage)
        = ⨆ k, ∑' q1, rnd q1 * ∑' q2, rnd q2 * cfgReturns (RRF q1 q2 0 ⟨eα,ep⟩) "experiment" startMessage k := by
      simp_rw [ReturnsToExperiment_eq_iSup]
      rw [tsum_congr (fun q1 => congrArg (fun t => rnd q1 * t)
        (tsum_mul_iSup_comm rnd (fun k q2 => cfgReturns (RRF q1 q2 0 ⟨eα,ep⟩) "experiment" startMessage k) (fun q2 => cfgReturns_monotone _ _ _)))]
      rw [tsum_mul_iSup_comm rnd (fun k q1 => ∑' q2, rnd q2 * cfgReturns (RRF q1 q2 0 ⟨eα,ep⟩) "experiment" startMessage k) hmono]
    rw [hcomm]
    exact iSup_le (fun k => pull_ge_0 k 0 0 eα ep "experiment" startMessage hn (by simp [startMessage]) sOK_experiment)
  · have hd : ∀ q1 q2, detReal ⟨eα,ep⟩ q1 q2 = 0 := fun q1 q2 => RTE_stuck_real q1 q2 eα ep hn
    simp [hd]

-- Ideal-distro phase routers (rnd machines KEIdeal/KESim in the drawn states).
noncomputable def idealPinsRstD (kei : KEIdealState) (ks : KESimState) (env : SPin) : List SPin :=
  [ ⟨KEIdealState, { name := "keideal", machine := { state := kei, func := KEIdeal.func } }⟩,
    ⟨KESimState, { name := "kesim", machine := { state := ks, func := KESim.func } }⟩,
    ⟨Unit, DummyPt1Pin⟩,
    ⟨Unit, DummyPt2Pin⟩,
    ⟨Unit, DummyFwd1Pin⟩,
    ⟨Unit, DummyFwd2Pin⟩,
    env ]

noncomputable def RID (q2 q3 : Nat) (i : ℕ) (env : SPin) : Router :=
  { pins := match i with
    | 0 => idealPinsRstD KEIdealState.WaitReq1 KESimState.WaitReq1 env
    | 1 => idealPinsRstD KEIdealState.WaitSim1 KESimState.WaitAdv1 env
    | 2 => idealPinsRstD (KEIdealState.WaitReq2 q3) (KESimState.WaitReq2 q2) env
    | 3 => idealPinsRstD (KEIdealState.WaitSim2 q3) KESimState.WaitAdv2 env
    | _ => idealPinsRstD KEIdealState.Done KESimState.Done env
    , wires := idealWires }

theorem delivIdealD_gen (kei : KEIdealState) (ks : KESimState)
    (eα : Type) (ep : Pin eα) (s : String) (m : Message)
    (henv : ep.name = "env") (hm : m.destination_name = "env") (hs : sOK s) :
    Router.route {pins := idealPinsRstD kei ks ⟨eα,ep⟩, wires := idealWires} s m
    = (ep.machine.func s m ep.machine.state).bind (fun x =>
        PMF.pure ({pins := idealPinsRstD kei ks ⟨eα, envStep ep x.2⟩, wires := idealWires}, "env", x.1)) := by
  rcases hs with h|h|h|h|h|h <;> subst h <;>
    simp [idealPinsRstD, idealWires, Router.route, Pin.invoke, envStep, changePinOfName,
      DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin, hm, henv, List.find?, List.map,
      Finset.mem_insert, Finset.mem_singleton, bind]

theorem delivIdealD (q2 q3 : Nat) (i : ℕ) (hi : i ≤ 4) (eα : Type) (ep : Pin eα) (s : String) (m : Message)
    (henv : ep.name = "env") (hm : m.destination_name = "env") (hs : sOK s) :
    Router.route (RID q2 q3 i ⟨eα,ep⟩) s m
    = (ep.machine.func s m ep.machine.state).bind (fun x =>
        PMF.pure (RID q2 q3 i ⟨eα, envStep ep x.2⟩, "env", x.1)) := by
  rcases i with _|_|_|_|_|i
  · exact delivIdealD_gen _ _ eα ep s m henv hm hs
  · exact delivIdealD_gen _ _ eα ep s m henv hm hs
  · exact delivIdealD_gen _ _ eα ep s m henv hm hs
  · exact delivIdealD_gen _ _ eα ep s m henv hm hs
  · exact delivIdealD_gen _ _ eα ep s m henv hm hs
  · omega

-- ===========================================================================
-- ID-peels: ideal-distro post-draw steps (+3 error, +4 advance).
-- ===========================================================================
theorem peelID_0_pt2 (q2 q3 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RID q2 q3 0 ⟨eα,ep⟩) "env" ({destination_name := "pt2", content := c} : Message) (n+3)
    = cfgReturns (RID q2 q3 0 ⟨eα,ep⟩) "pt2" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RID, idealPinsRstD, idealWires, Router.route, KEIdeal, KESim, DummyPt, DummyAdv, DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelID_0_fwd1 (q2 q3 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RID q2 q3 0 ⟨eα,ep⟩) "env" ({destination_name := "fwd1", content := c} : Message) (n+3)
    = cfgReturns (RID q2 q3 0 ⟨eα,ep⟩) "fwd1" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RID, idealPinsRstD, idealWires, Router.route, KEIdeal, KESim, DummyPt, DummyAdv, DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelID_0_fwd2 (q2 q3 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RID q2 q3 0 ⟨eα,ep⟩) "env" ({destination_name := "fwd2", content := c} : Message) (n+3)
    = cfgReturns (RID q2 q3 0 ⟨eα,ep⟩) "fwd2" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RID, idealPinsRstD, idealWires, Router.route, KEIdeal, KESim, DummyPt, DummyAdv, DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelID_1_pt1 (q2 q3 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RID q2 q3 1 ⟨eα,ep⟩) "env" ({destination_name := "pt1", content := c} : Message) (n+3)
    = cfgReturns (RID q2 q3 1 ⟨eα,ep⟩) "pt1" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RID, idealPinsRstD, idealWires, Router.route, KEIdeal, KESim, DummyPt, DummyAdv, DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelID_1_pt2 (q2 q3 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RID q2 q3 1 ⟨eα,ep⟩) "env" ({destination_name := "pt2", content := c} : Message) (n+3)
    = cfgReturns (RID q2 q3 1 ⟨eα,ep⟩) "pt2" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RID, idealPinsRstD, idealWires, Router.route, KEIdeal, KESim, DummyPt, DummyAdv, DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelID_1_fwd2 (q2 q3 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RID q2 q3 1 ⟨eα,ep⟩) "env" ({destination_name := "fwd2", content := c} : Message) (n+3)
    = cfgReturns (RID q2 q3 1 ⟨eα,ep⟩) "fwd2" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RID, idealPinsRstD, idealWires, Router.route, KEIdeal, KESim, DummyPt, DummyAdv, DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelID_2_pt1 (q2 q3 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RID q2 q3 2 ⟨eα,ep⟩) "env" ({destination_name := "pt1", content := c} : Message) (n+3)
    = cfgReturns (RID q2 q3 2 ⟨eα,ep⟩) "pt1" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RID, idealPinsRstD, idealWires, Router.route, KEIdeal, KESim, DummyPt, DummyAdv, DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelID_2_fwd1 (q2 q3 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RID q2 q3 2 ⟨eα,ep⟩) "env" ({destination_name := "fwd1", content := c} : Message) (n+3)
    = cfgReturns (RID q2 q3 2 ⟨eα,ep⟩) "fwd1" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RID, idealPinsRstD, idealWires, Router.route, KEIdeal, KESim, DummyPt, DummyAdv, DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelID_2_fwd2 (q2 q3 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RID q2 q3 2 ⟨eα,ep⟩) "env" ({destination_name := "fwd2", content := c} : Message) (n+3)
    = cfgReturns (RID q2 q3 2 ⟨eα,ep⟩) "fwd2" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RID, idealPinsRstD, idealWires, Router.route, KEIdeal, KESim, DummyPt, DummyAdv, DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelID_3_pt1 (q2 q3 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RID q2 q3 3 ⟨eα,ep⟩) "env" ({destination_name := "pt1", content := c} : Message) (n+3)
    = cfgReturns (RID q2 q3 3 ⟨eα,ep⟩) "pt1" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RID, idealPinsRstD, idealWires, Router.route, KEIdeal, KESim, DummyPt, DummyAdv, DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelID_3_pt2 (q2 q3 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RID q2 q3 3 ⟨eα,ep⟩) "env" ({destination_name := "pt2", content := c} : Message) (n+3)
    = cfgReturns (RID q2 q3 3 ⟨eα,ep⟩) "pt2" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RID, idealPinsRstD, idealWires, Router.route, KEIdeal, KESim, DummyPt, DummyAdv, DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelID_3_fwd1 (q2 q3 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RID q2 q3 3 ⟨eα,ep⟩) "env" ({destination_name := "fwd1", content := c} : Message) (n+3)
    = cfgReturns (RID q2 q3 3 ⟨eα,ep⟩) "fwd1" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RID, idealPinsRstD, idealWires, Router.route, KEIdeal, KESim, DummyPt, DummyAdv, DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelID_4_pt1 (q2 q3 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RID q2 q3 4 ⟨eα,ep⟩) "env" ({destination_name := "pt1", content := c} : Message) (n+3)
    = cfgReturns (RID q2 q3 4 ⟨eα,ep⟩) "pt1" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RID, idealPinsRstD, idealWires, Router.route, KEIdeal, KESim, DummyPt, DummyAdv, DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelID_4_pt2 (q2 q3 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RID q2 q3 4 ⟨eα,ep⟩) "env" ({destination_name := "pt2", content := c} : Message) (n+3)
    = cfgReturns (RID q2 q3 4 ⟨eα,ep⟩) "pt2" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RID, idealPinsRstD, idealWires, Router.route, KEIdeal, KESim, DummyPt, DummyAdv, DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelID_4_fwd1 (q2 q3 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RID q2 q3 4 ⟨eα,ep⟩) "env" ({destination_name := "fwd1", content := c} : Message) (n+3)
    = cfgReturns (RID q2 q3 4 ⟨eα,ep⟩) "fwd1" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RID, idealPinsRstD, idealWires, Router.route, KEIdeal, KESim, DummyPt, DummyAdv, DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelID_4_fwd2 (q2 q3 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RID q2 q3 4 ⟨eα,ep⟩) "env" ({destination_name := "fwd2", content := c} : Message) (n+3)
    = cfgReturns (RID q2 q3 4 ⟨eα,ep⟩) "fwd2" ({destination_name := "env", content := contentError} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RID, idealPinsRstD, idealWires, Router.route, KEIdeal, KESim, DummyPt, DummyAdv, DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelID_2_pt2 (q2 q3 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RID q2 q3 2 ⟨eα,ep⟩) "env" ({destination_name := "pt2", content := c} : Message) (n+4)
    = cfgReturns (RID q2 q3 3 ⟨eα,ep⟩) "fwd2"
        ({destination_name := "env",
          content := string2selfdelimitingString "pt2"
            ++ toString ({destination_name := "pt1", content := pwr "g" q2} : Message)} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RID, idealPinsRstD, idealWires, Router.route, KEIdeal, KESim, DummyPt, DummyAdv, DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelID_3_fwd2 (q2 q3 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RID q2 q3 3 ⟨eα,ep⟩) "env" ({destination_name := "fwd2", content := c} : Message) (n+4)
    = cfgReturns (RID q2 q3 4 ⟨eα,ep⟩) "pt1"
        ({destination_name := "env", content := pwr "g" q3} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RID, idealPinsRstD, idealWires, Router.route, KEIdeal, KESim, DummyPt, DummyAdv, DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, bind, PMF.pure_bind]

theorem peelID_other (i : ℕ) (q2 q3 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env")
    (md mc : String) (h1 : md ≠ "experiment") (h2 : md ≠ "pt1") (h3 : md ≠ "pt2")
    (h4 : md ≠ "fwd1") (h5 : md ≠ "fwd2") (h6 : md ≠ "env") (n : ℕ) :
    cfgReturns (RID q2 q3 i ⟨eα,ep⟩) "env" ({destination_name := md, content := mc} : Message) (n+1)
    = cfgReturns (RID q2 q3 i ⟨eα,ep⟩) "env"
        (destinationEnvMessage ({destination_name := md, content := mc} : Message)) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RID, idealPinsRstD, idealWires, Router.route, KEIdeal, KESim, DummyPt, DummyAdv, DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin, Pin.invoke, changePinOfName, destinationEnvMessage, Machine.errorMessage2sender, List.find?, List.map, henv, h1, h2, h3, h4, h5, h6, Finset.mem_insert, Finset.mem_singleton, bind, PMF.pure_bind]


theorem funcIrrel_ideal_le (k1 : String) (q2 q3 : Nat) : ∀ (k i : ℕ) (eα : Type) (ep : Pin eα) (s : String) (m : Message),
    ep.name = "env" → m.destination_name = "env" → sOK s → 2 ≤ i → i ≤ 4 →
    cfgReturns (RID q2 q3 i ⟨eα,ep⟩) s m k ≤ ReturnsToExperiment (RIF k1 (pwr "g" q2) (pwr "g" q3) i ⟨eα,ep⟩) s m := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i eα ep s m henv hm hs h2i hi
    cases k with
    | zero => rw [cfgReturns_zero_nexp _ _ _ (by rw [hm]; decide)]; exact zero_le
    | succ n =>
      rw [cfgReturns_env_deliver_gen _ _ _ (by rw [hm]; decide) (delivIdealD q2 q3 i hi eα ep s m henv hm hs) n,
          ReturnsToExperiment_env_deliver_gen _ _ _ (by rw [hm]; decide) (delivIdeal k1 (pwr "g" q2) (pwr "g" q3) i hi eα ep s m henv hm hs)]
      apply ENNReal.tsum_le_tsum
      intro x
      apply mul_le_mul_left'
      obtain ⟨⟨md, mc⟩, ns⟩ := x
      set ep2 := envStep ep ns with hep2
      have hname2 : ep2.name = "env" := by rw [hep2]; exact envStep_name ep ns henv
      rcases i with _|_|_|_|_|i
      · omega
      · omega
      · -- phase 2
        by_cases h_exp : md = "experiment"
        · subst h_exp
          rw [cfgReturns_exp _ _ _ rfl, ReturnsToExperiment_eq_iSup]
          exact le_iSup_of_le 0 (le_of_eq (cfgReturns_exp _ _ _ rfl 0).symm)
        by_cases h_env : md = "env"
        · subst h_env
          exact ih n (Nat.lt_succ_self n) 2 eα ep2 "env" ⟨"env", mc⟩ hname2 rfl sOK_env (by omega) (by omega)
        by_cases h_pt1 : md = "pt1"
        · subst h_pt1
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 3 3 n
            (peelID_2_pt1 q2 q3 eα ep2 hname2 mc) (peelI_2_pt1 k1 (pwr "g" q2) (pwr "g" q3) eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 2 eα ep2 "pt1" ⟨"env", contentError⟩ hname2 rfl sOK_pt1 (by omega) (by omega))
        by_cases h_pt2 : md = "pt2"
        · subst h_pt2
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 4 4 n
            (peelID_2_pt2 q2 q3 eα ep2 hname2 mc) (peelI_2_pt2 k1 (pwr "g" q2) (pwr "g" q3) eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 3 eα ep2 "fwd2" ⟨"env", string2selfdelimitingString "pt2" ++ toString ({destination_name := "pt1", content := pwr "g" q2} : Message)⟩ hname2 rfl sOK_fwd2 (by omega) (by omega))
        by_cases h_fwd1 : md = "fwd1"
        · subst h_fwd1
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 3 3 n
            (peelID_2_fwd1 q2 q3 eα ep2 hname2 mc) (peelI_2_fwd1 k1 (pwr "g" q2) (pwr "g" q3) eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 2 eα ep2 "fwd1" ⟨"env", contentError⟩ hname2 rfl sOK_fwd1 (by omega) (by omega))
        by_cases h_fwd2 : md = "fwd2"
        · subst h_fwd2
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 3 3 n
            (peelID_2_fwd2 q2 q3 eα ep2 hname2 mc) (peelI_2_fwd2 k1 (pwr "g" q2) (pwr "g" q3) eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 2 eα ep2 "fwd2" ⟨"env", contentError⟩ hname2 rfl sOK_fwd2 (by omega) (by omega))
        · exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 1 n
            (peelID_other 2 q2 q3 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env) (peelI_other k1 (pwr "g" q2) (pwr "g" q3) 2 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env)
            (ih n (Nat.lt_succ_self n) 2 eα ep2 "env" (destinationEnvMessage ⟨md, mc⟩) hname2 (by simp [destinationEnvMessage]) sOK_env (by omega) (by omega))
      · -- phase 3
        by_cases h_exp : md = "experiment"
        · subst h_exp
          rw [cfgReturns_exp _ _ _ rfl, ReturnsToExperiment_eq_iSup]
          exact le_iSup_of_le 0 (le_of_eq (cfgReturns_exp _ _ _ rfl 0).symm)
        by_cases h_env : md = "env"
        · subst h_env
          exact ih n (Nat.lt_succ_self n) 3 eα ep2 "env" ⟨"env", mc⟩ hname2 rfl sOK_env (by omega) (by omega)
        by_cases h_pt1 : md = "pt1"
        · subst h_pt1
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 3 3 n
            (peelID_3_pt1 q2 q3 eα ep2 hname2 mc) (peelI_3_pt1 k1 (pwr "g" q2) (pwr "g" q3) eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 3 eα ep2 "pt1" ⟨"env", contentError⟩ hname2 rfl sOK_pt1 (by omega) (by omega))
        by_cases h_pt2 : md = "pt2"
        · subst h_pt2
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 3 3 n
            (peelID_3_pt2 q2 q3 eα ep2 hname2 mc) (peelI_3_pt2 k1 (pwr "g" q2) (pwr "g" q3) eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 3 eα ep2 "pt2" ⟨"env", contentError⟩ hname2 rfl sOK_pt2 (by omega) (by omega))
        by_cases h_fwd1 : md = "fwd1"
        · subst h_fwd1
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 3 3 n
            (peelID_3_fwd1 q2 q3 eα ep2 hname2 mc) (peelI_3_fwd1 k1 (pwr "g" q2) (pwr "g" q3) eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 3 eα ep2 "fwd1" ⟨"env", contentError⟩ hname2 rfl sOK_fwd1 (by omega) (by omega))
        by_cases h_fwd2 : md = "fwd2"
        · subst h_fwd2
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 4 4 n
            (peelID_3_fwd2 q2 q3 eα ep2 hname2 mc) (peelI_3_fwd2 k1 (pwr "g" q2) (pwr "g" q3) eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 4 eα ep2 "pt1" ⟨"env", pwr "g" q3⟩ hname2 rfl sOK_pt1 (by omega) (by omega))
        · exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 1 n
            (peelID_other 3 q2 q3 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env) (peelI_other k1 (pwr "g" q2) (pwr "g" q3) 3 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env)
            (ih n (Nat.lt_succ_self n) 3 eα ep2 "env" (destinationEnvMessage ⟨md, mc⟩) hname2 (by simp [destinationEnvMessage]) sOK_env (by omega) (by omega))
      · -- phase 4
        by_cases h_exp : md = "experiment"
        · subst h_exp
          rw [cfgReturns_exp _ _ _ rfl, ReturnsToExperiment_eq_iSup]
          exact le_iSup_of_le 0 (le_of_eq (cfgReturns_exp _ _ _ rfl 0).symm)
        by_cases h_env : md = "env"
        · subst h_env
          exact ih n (Nat.lt_succ_self n) 4 eα ep2 "env" ⟨"env", mc⟩ hname2 rfl sOK_env (by omega) (by omega)
        by_cases h_pt1 : md = "pt1"
        · subst h_pt1
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 3 3 n
            (peelID_4_pt1 q2 q3 eα ep2 hname2 mc) (peelI_4_pt1 k1 (pwr "g" q2) (pwr "g" q3) eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 4 eα ep2 "pt1" ⟨"env", contentError⟩ hname2 rfl sOK_pt1 (by omega) (by omega))
        by_cases h_pt2 : md = "pt2"
        · subst h_pt2
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 3 3 n
            (peelID_4_pt2 q2 q3 eα ep2 hname2 mc) (peelI_4_pt2 k1 (pwr "g" q2) (pwr "g" q3) eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 4 eα ep2 "pt2" ⟨"env", contentError⟩ hname2 rfl sOK_pt2 (by omega) (by omega))
        by_cases h_fwd1 : md = "fwd1"
        · subst h_fwd1
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 3 3 n
            (peelID_4_fwd1 q2 q3 eα ep2 hname2 mc) (peelI_4_fwd1 k1 (pwr "g" q2) (pwr "g" q3) eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 4 eα ep2 "fwd1" ⟨"env", contentError⟩ hname2 rfl sOK_fwd1 (by omega) (by omega))
        by_cases h_fwd2 : md = "fwd2"
        · subst h_fwd2
          exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 3 3 n
            (peelID_4_fwd2 q2 q3 eα ep2 hname2 mc) (peelI_4_fwd2 k1 (pwr "g" q2) (pwr "g" q3) eα ep2 hname2 mc)
            (ih n (Nat.lt_succ_self n) 4 eα ep2 "fwd2" ⟨"env", contentError⟩ hname2 rfl sOK_fwd2 (by omega) (by omega))
        · exact step_bound _ _ _ _ _ _ _ _ _ _ _ _ 1 1 n
            (peelID_other 4 q2 q3 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env) (peelI_other k1 (pwr "g" q2) (pwr "g" q3) 4 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env)
            (ih n (Nat.lt_succ_self n) 4 eα ep2 "env" (destinationEnvMessage ⟨md, mc⟩) hname2 (by simp [destinationEnvMessage]) sOK_env (by omega) (by omega))
      · exact absurd hi (by omega)

-- Ideal draw peels: KESim draws q1 at phase 0; KESim draws q2 and KEIdeal draws q3 at phase 1.
theorem peelID_0_pt1 (q2 q3 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RID q2 q3 0 ⟨eα,ep⟩) "env" ({destination_name := "pt1", content := c} : Message) (n+4)
    = ∑' q1, rnd q1 * cfgReturns (RID q2 q3 1 ⟨eα,ep⟩) "fwd1"
        ({destination_name := "env",
          content := string2selfdelimitingString "pt1"
            ++ toString ({destination_name := "pt2", content := pwr "g" q1} : Message)} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RID, idealPinsRstD, idealWires, Router.route,
    KEIdeal, KESim, DummyPt, DummyAdv, DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin,
    Pin.invoke, changePinOfName, Machine.errorMessage2sender, List.find?, List.map, henv,
    bind, PMF.pure_bind, PMF.bind_apply]

theorem peelID_1_fwd1 (q2 q3 : Nat) (eα : Type) (ep : Pin eα) (henv : ep.name = "env") (c : String) (n : ℕ) :
    cfgReturns (RID q2 q3 1 ⟨eα,ep⟩) "env" ({destination_name := "fwd1", content := c} : Message) (n+4)
    = ∑' a, rnd a * ∑' b, rnd b * cfgReturns (RID a b 2 ⟨eα,ep⟩) "pt2"
        ({destination_name := "env", content := pwr "g" b} : Message) n := by
  simp [cfgReturns, ReturnsToExperiment_within_n_steps, RID, idealPinsRstD, idealWires, Router.route,
    KEIdeal, KESim, DummyPt, DummyAdv, DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin,
    Pin.invoke, changePinOfName, Machine.errorMessage2sender, List.find?, List.map, henv,
    bind, PMF.pure_bind, PMF.bind_apply]

-- pull at ideal phase 1: factor Pt2/KEIdeal coins (double draw).
theorem pull_le_ideal_1 (k1 : String) : ∀ (k : ℕ) (q2 q3 : Nat) (eα : Type) (ep : Pin eα) (s : String) (m : Message),
    ep.name = "env" → m.destination_name = "env" → sOK s →
    cfgReturns (RID q2 q3 1 ⟨eα,ep⟩) s m k
      ≤ ∑' a, rnd a * ∑' b, rnd b * ReturnsToExperiment (RIF k1 (pwr "g" a) (pwr "g" b) 1 ⟨eα,ep⟩) s m := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro q2 q3 eα ep s m henv hm hs
    cases k with
    | zero => rw [cfgReturns_zero_nexp _ _ _ (by rw [hm]; decide)]; exact zero_le
    | succ n =>
      rw [cfgReturns_env_deliver_gen _ _ _ (by rw [hm]; decide) (delivIdealD q2 q3 1 (by omega) eα ep s m henv hm hs) n]
      have hR : (∑' a, rnd a * ∑' b, rnd b * ReturnsToExperiment (RIF k1 (pwr "g" a) (pwr "g" b) 1 ⟨eα,ep⟩) s m)
          = ∑' x, (ep.machine.func s m ep.machine.state) x
              * ∑' a, rnd a * ∑' b, rnd b * ReturnsToExperiment (RIF k1 (pwr "g" a) (pwr "g" b) 1 ⟨eα, envStep ep x.2⟩) "env" x.1 := by
        have hd : ∀ a b, ReturnsToExperiment (RIF k1 (pwr "g" a) (pwr "g" b) 1 ⟨eα,ep⟩) s m
            = ∑' x, (ep.machine.func s m ep.machine.state) x * ReturnsToExperiment (RIF k1 (pwr "g" a) (pwr "g" b) 1 ⟨eα, envStep ep x.2⟩) "env" x.1 :=
          fun a b => ReturnsToExperiment_env_deliver_gen _ _ _ (by rw [hm]; decide) (delivIdeal k1 (pwr "g" a) (pwr "g" b) 1 (by omega) eα ep s m henv hm hs)
        simp_rw [hd]
        rw [tsum_congr (fun a => congrArg (fun t => rnd a * t)
          (tsum_swap_mul (ep.machine.func s m ep.machine.state) rnd
            (fun b x => ReturnsToExperiment (RIF k1 (pwr "g" a) (pwr "g" b) 1 ⟨eα, envStep ep x.2⟩) "env" x.1)))]
        rw [tsum_swap_mul (ep.machine.func s m ep.machine.state) rnd
          (fun a x => ∑' b, rnd b * ReturnsToExperiment (RIF k1 (pwr "g" a) (pwr "g" b) 1 ⟨eα, envStep ep x.2⟩) "env" x.1)]
      rw [hR]
      apply ENNReal.tsum_le_tsum
      intro x
      apply mul_le_mul_left'
      obtain ⟨⟨md, mc⟩, ns⟩ := x
      set ep2 := envStep ep ns with hep2
      have hname2 : ep2.name = "env" := by rw [hep2]; exact envStep_name ep ns henv
      by_cases h_exp : md = "experiment"
      · subst h_exp
        rw [cfgReturns_exp _ _ _ rfl]
        have hR1 : ∀ a b, ReturnsToExperiment (RIF k1 (pwr "g" a) (pwr "g" b) 1 ⟨eα,ep2⟩) "env" ⟨"experiment", mc⟩ = 1 :=
          fun a b => by
            rw [ReturnsToExperiment_eq_iSup]
            exact le_antisymm (iSup_le (fun j => le_of_eq (cfgReturns_exp _ _ _ rfl j)))
              (le_iSup_of_le 0 (le_of_eq (cfgReturns_exp _ _ _ rfl 0).symm))
        simp [hR1, rnd.tsum_coe]
      by_cases h_env : md = "env"
      · subst h_env
        exact ih n (Nat.lt_succ_self n) q2 q3 eα ep2 "env" ⟨"env", mc⟩ hname2 rfl sOK_env
      by_cases h_pt1 : md = "pt1"
      · subst h_pt1
        calc cfgReturns (RID q2 q3 1 ⟨eα,ep2⟩) "env" ⟨"pt1", mc⟩ n
            ≤ cfgReturns (RID q2 q3 1 ⟨eα,ep2⟩) "pt1" ⟨"env", contentError⟩ n := by
              calc cfgReturns (RID q2 q3 1 ⟨eα,ep2⟩) "env" ⟨"pt1", mc⟩ n
                  ≤ cfgReturns (RID q2 q3 1 ⟨eα,ep2⟩) "env" ⟨"pt1", mc⟩ (n+3) := cfgReturns_le_add _ _ _ _ _
                _ = cfgReturns (RID q2 q3 1 ⟨eα,ep2⟩) "pt1" ⟨"env", contentError⟩ n := peelID_1_pt1 q2 q3 eα ep2 hname2 mc n
          _ ≤ ∑' a, rnd a * ∑' b, rnd b * ReturnsToExperiment (RIF k1 (pwr "g" a) (pwr "g" b) 1 ⟨eα,ep2⟩) "pt1" ⟨"env", contentError⟩ :=
              ih n (Nat.lt_succ_self n) q2 q3 eα ep2 "pt1" ⟨"env", contentError⟩ hname2 rfl sOK_pt1
          _ = ∑' a, rnd a * ∑' b, rnd b * ReturnsToExperiment (RIF k1 (pwr "g" a) (pwr "g" b) 1 ⟨eα,ep2⟩) "env" ⟨"pt1", mc⟩ := by
              refine tsum_congr (fun a => congrArg _ (tsum_congr (fun b => congrArg _ ?_)))
              exact (ReturnsToExperiment_of_peel 3 (peelI_1_pt1 k1 (pwr "g" a) (pwr "g" b) eα ep2 hname2 mc)).symm
      by_cases h_pt2 : md = "pt2"
      · subst h_pt2
        calc cfgReturns (RID q2 q3 1 ⟨eα,ep2⟩) "env" ⟨"pt2", mc⟩ n
            ≤ cfgReturns (RID q2 q3 1 ⟨eα,ep2⟩) "pt2" ⟨"env", contentError⟩ n := by
              calc cfgReturns (RID q2 q3 1 ⟨eα,ep2⟩) "env" ⟨"pt2", mc⟩ n
                  ≤ cfgReturns (RID q2 q3 1 ⟨eα,ep2⟩) "env" ⟨"pt2", mc⟩ (n+3) := cfgReturns_le_add _ _ _ _ _
                _ = cfgReturns (RID q2 q3 1 ⟨eα,ep2⟩) "pt2" ⟨"env", contentError⟩ n := peelID_1_pt2 q2 q3 eα ep2 hname2 mc n
          _ ≤ ∑' a, rnd a * ∑' b, rnd b * ReturnsToExperiment (RIF k1 (pwr "g" a) (pwr "g" b) 1 ⟨eα,ep2⟩) "pt2" ⟨"env", contentError⟩ :=
              ih n (Nat.lt_succ_self n) q2 q3 eα ep2 "pt2" ⟨"env", contentError⟩ hname2 rfl sOK_pt2
          _ = ∑' a, rnd a * ∑' b, rnd b * ReturnsToExperiment (RIF k1 (pwr "g" a) (pwr "g" b) 1 ⟨eα,ep2⟩) "env" ⟨"pt2", mc⟩ := by
              refine tsum_congr (fun a => congrArg _ (tsum_congr (fun b => congrArg _ ?_)))
              exact (ReturnsToExperiment_of_peel 3 (peelI_1_pt2 k1 (pwr "g" a) (pwr "g" b) eα ep2 hname2 mc)).symm
      by_cases h_fwd1 : md = "fwd1"
      · subst h_fwd1
        calc cfgReturns (RID q2 q3 1 ⟨eα,ep2⟩) "env" ⟨"fwd1", mc⟩ n
            ≤ ∑' a, rnd a * ∑' b, rnd b * cfgReturns (RID a b 2 ⟨eα,ep2⟩) "pt2" ⟨"env", pwr "g" b⟩ n := by
              calc cfgReturns (RID q2 q3 1 ⟨eα,ep2⟩) "env" ⟨"fwd1", mc⟩ n
                  ≤ cfgReturns (RID q2 q3 1 ⟨eα,ep2⟩) "env" ⟨"fwd1", mc⟩ (n+4) := cfgReturns_le_add _ _ _ _ _
                _ = ∑' a, rnd a * ∑' b, rnd b * cfgReturns (RID a b 2 ⟨eα,ep2⟩) "pt2" ⟨"env", pwr "g" b⟩ n := peelID_1_fwd1 q2 q3 eα ep2 hname2 mc n
          _ ≤ ∑' a, rnd a * ∑' b, rnd b * ReturnsToExperiment (RIF k1 (pwr "g" a) (pwr "g" b) 2 ⟨eα,ep2⟩) "pt2" ⟨"env", pwr "g" b⟩ := by
              apply ENNReal.tsum_le_tsum; intro a; apply mul_le_mul_left'
              apply ENNReal.tsum_le_tsum; intro b; apply mul_le_mul_left'
              exact funcIrrel_ideal_le k1 a b n 2 eα ep2 "pt2" ⟨"env", pwr "g" b⟩ hname2 rfl sOK_pt2 (by omega) (by omega)
          _ = ∑' a, rnd a * ∑' b, rnd b * ReturnsToExperiment (RIF k1 (pwr "g" a) (pwr "g" b) 1 ⟨eα,ep2⟩) "env" ⟨"fwd1", mc⟩ := by
              refine tsum_congr (fun a => congrArg _ (tsum_congr (fun b => congrArg _ ?_)))
              exact (ReturnsToExperiment_of_peel 4 (peelI_1_fwd1 k1 (pwr "g" a) (pwr "g" b) eα ep2 hname2 mc)).symm
      by_cases h_fwd2 : md = "fwd2"
      · subst h_fwd2
        calc cfgReturns (RID q2 q3 1 ⟨eα,ep2⟩) "env" ⟨"fwd2", mc⟩ n
            ≤ cfgReturns (RID q2 q3 1 ⟨eα,ep2⟩) "fwd2" ⟨"env", contentError⟩ n := by
              calc cfgReturns (RID q2 q3 1 ⟨eα,ep2⟩) "env" ⟨"fwd2", mc⟩ n
                  ≤ cfgReturns (RID q2 q3 1 ⟨eα,ep2⟩) "env" ⟨"fwd2", mc⟩ (n+3) := cfgReturns_le_add _ _ _ _ _
                _ = cfgReturns (RID q2 q3 1 ⟨eα,ep2⟩) "fwd2" ⟨"env", contentError⟩ n := peelID_1_fwd2 q2 q3 eα ep2 hname2 mc n
          _ ≤ ∑' a, rnd a * ∑' b, rnd b * ReturnsToExperiment (RIF k1 (pwr "g" a) (pwr "g" b) 1 ⟨eα,ep2⟩) "fwd2" ⟨"env", contentError⟩ :=
              ih n (Nat.lt_succ_self n) q2 q3 eα ep2 "fwd2" ⟨"env", contentError⟩ hname2 rfl sOK_fwd2
          _ = ∑' a, rnd a * ∑' b, rnd b * ReturnsToExperiment (RIF k1 (pwr "g" a) (pwr "g" b) 1 ⟨eα,ep2⟩) "env" ⟨"fwd2", mc⟩ := by
              refine tsum_congr (fun a => congrArg _ (tsum_congr (fun b => congrArg _ ?_)))
              exact (ReturnsToExperiment_of_peel 3 (peelI_1_fwd2 k1 (pwr "g" a) (pwr "g" b) eα ep2 hname2 mc)).symm
      · calc cfgReturns (RID q2 q3 1 ⟨eα,ep2⟩) "env" ⟨md, mc⟩ n
            ≤ cfgReturns (RID q2 q3 1 ⟨eα,ep2⟩) "env" (destinationEnvMessage ⟨md, mc⟩) n := by
              calc cfgReturns (RID q2 q3 1 ⟨eα,ep2⟩) "env" ⟨md, mc⟩ n
                  ≤ cfgReturns (RID q2 q3 1 ⟨eα,ep2⟩) "env" ⟨md, mc⟩ (n+1) := cfgReturns_le_add _ _ _ _ _
                _ = cfgReturns (RID q2 q3 1 ⟨eα,ep2⟩) "env" (destinationEnvMessage ⟨md, mc⟩) n := peelID_other 1 q2 q3 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env n
          _ ≤ ∑' a, rnd a * ∑' b, rnd b * ReturnsToExperiment (RIF k1 (pwr "g" a) (pwr "g" b) 1 ⟨eα,ep2⟩) "env" (destinationEnvMessage ⟨md, mc⟩) :=
              ih n (Nat.lt_succ_self n) q2 q3 eα ep2 "env" (destinationEnvMessage ⟨md, mc⟩) hname2 (by simp [destinationEnvMessage]) sOK_env
          _ = ∑' a, rnd a * ∑' b, rnd b * ReturnsToExperiment (RIF k1 (pwr "g" a) (pwr "g" b) 1 ⟨eα,ep2⟩) "env" ⟨md, mc⟩ := by
              refine tsum_congr (fun a => congrArg _ (tsum_congr (fun b => congrArg _ ?_)))
              exact (ReturnsToExperiment_of_peel 1 (peelI_other k1 (pwr "g" a) (pwr "g" b) 1 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env)).symm

-- pull at ideal phase 0: factor KESim's first coin, then delegate to pull_le_ideal_1.
theorem pull_le_ideal_0 : ∀ (k : ℕ) (q2 q3 : Nat) (eα : Type) (ep : Pin eα) (s : String) (m : Message),
    ep.name = "env" → m.destination_name = "env" → sOK s →
    cfgReturns (RID q2 q3 0 ⟨eα,ep⟩) s m k
      ≤ ∑' r1, rnd r1 * ∑' a, rnd a * ∑' b, rnd b
          * ReturnsToExperiment (RIF (pwr "g" r1) (pwr "g" a) (pwr "g" b) 0 ⟨eα,ep⟩) s m := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro q2 q3 eα ep s m henv hm hs
    cases k with
    | zero => rw [cfgReturns_zero_nexp _ _ _ (by rw [hm]; decide)]; exact zero_le
    | succ n =>
      rw [cfgReturns_env_deliver_gen _ _ _ (by rw [hm]; decide) (delivIdealD q2 q3 0 (by omega) eα ep s m henv hm hs) n]
      have hR : (∑' r1, rnd r1 * ∑' a, rnd a * ∑' b, rnd b * ReturnsToExperiment (RIF (pwr "g" r1) (pwr "g" a) (pwr "g" b) 0 ⟨eα,ep⟩) s m)
          = ∑' x, (ep.machine.func s m ep.machine.state) x
              * ∑' r1, rnd r1 * ∑' a, rnd a * ∑' b, rnd b * ReturnsToExperiment (RIF (pwr "g" r1) (pwr "g" a) (pwr "g" b) 0 ⟨eα, envStep ep x.2⟩) "env" x.1 := by
        have hd : ∀ r1 a b, ReturnsToExperiment (RIF (pwr "g" r1) (pwr "g" a) (pwr "g" b) 0 ⟨eα,ep⟩) s m
            = ∑' x, (ep.machine.func s m ep.machine.state) x * ReturnsToExperiment (RIF (pwr "g" r1) (pwr "g" a) (pwr "g" b) 0 ⟨eα, envStep ep x.2⟩) "env" x.1 :=
          fun r1 a b => ReturnsToExperiment_env_deliver_gen _ _ _ (by rw [hm]; decide) (delivIdeal (pwr "g" r1) (pwr "g" a) (pwr "g" b) 0 (by omega) eα ep s m henv hm hs)
        simp_rw [hd]
        rw [tsum_congr (fun r1 => congrArg (fun t => rnd r1 * t) (tsum_congr (fun a => congrArg (fun t => rnd a * t)
          (tsum_swap_mul (ep.machine.func s m ep.machine.state) rnd
            (fun b x => ReturnsToExperiment (RIF (pwr "g" r1) (pwr "g" a) (pwr "g" b) 0 ⟨eα, envStep ep x.2⟩) "env" x.1)))))]
        rw [tsum_congr (fun r1 => congrArg (fun t => rnd r1 * t)
          (tsum_swap_mul (ep.machine.func s m ep.machine.state) rnd
            (fun a x => ∑' b, rnd b * ReturnsToExperiment (RIF (pwr "g" r1) (pwr "g" a) (pwr "g" b) 0 ⟨eα, envStep ep x.2⟩) "env" x.1)))]
        rw [tsum_swap_mul (ep.machine.func s m ep.machine.state) rnd
          (fun r1 x => ∑' a, rnd a * ∑' b, rnd b * ReturnsToExperiment (RIF (pwr "g" r1) (pwr "g" a) (pwr "g" b) 0 ⟨eα, envStep ep x.2⟩) "env" x.1)]
      rw [hR]
      apply ENNReal.tsum_le_tsum
      intro x
      apply mul_le_mul_left'
      obtain ⟨⟨md, mc⟩, ns⟩ := x
      set ep2 := envStep ep ns with hep2
      have hname2 : ep2.name = "env" := by rw [hep2]; exact envStep_name ep ns henv
      by_cases h_exp : md = "experiment"
      · subst h_exp
        rw [cfgReturns_exp _ _ _ rfl]
        have hR1 : ∀ r1 a b, ReturnsToExperiment (RIF (pwr "g" r1) (pwr "g" a) (pwr "g" b) 0 ⟨eα,ep2⟩) "env" ⟨"experiment", mc⟩ = 1 :=
          fun r1 a b => by
            rw [ReturnsToExperiment_eq_iSup]
            exact le_antisymm (iSup_le (fun j => le_of_eq (cfgReturns_exp _ _ _ rfl j)))
              (le_iSup_of_le 0 (le_of_eq (cfgReturns_exp _ _ _ rfl 0).symm))
        simp [hR1, rnd.tsum_coe]
      by_cases h_env : md = "env"
      · subst h_env
        exact ih n (Nat.lt_succ_self n) q2 q3 eα ep2 "env" ⟨"env", mc⟩ hname2 rfl sOK_env
      by_cases h_pt1 : md = "pt1"
      · subst h_pt1
        calc cfgReturns (RID q2 q3 0 ⟨eα,ep2⟩) "env" ⟨"pt1", mc⟩ n
            ≤ ∑' r1, rnd r1 * cfgReturns (RID q2 q3 1 ⟨eα,ep2⟩) "fwd1"
                ⟨"env", string2selfdelimitingString "pt1" ++ toString ({destination_name := "pt2", content := pwr "g" r1} : Message)⟩ n := by
              calc cfgReturns (RID q2 q3 0 ⟨eα,ep2⟩) "env" ⟨"pt1", mc⟩ n
                  ≤ cfgReturns (RID q2 q3 0 ⟨eα,ep2⟩) "env" ⟨"pt1", mc⟩ (n+4) := cfgReturns_le_add _ _ _ _ _
                _ = ∑' r1, rnd r1 * cfgReturns (RID q2 q3 1 ⟨eα,ep2⟩) "fwd1"
                      ⟨"env", string2selfdelimitingString "pt1" ++ toString ({destination_name := "pt2", content := pwr "g" r1} : Message)⟩ n := peelID_0_pt1 q2 q3 eα ep2 hname2 mc n
          _ ≤ ∑' r1, rnd r1 * ∑' a, rnd a * ∑' b, rnd b * ReturnsToExperiment (RIF (pwr "g" r1) (pwr "g" a) (pwr "g" b) 1 ⟨eα,ep2⟩) "fwd1"
                ⟨"env", string2selfdelimitingString "pt1" ++ toString ({destination_name := "pt2", content := pwr "g" r1} : Message)⟩ := by
              apply ENNReal.tsum_le_tsum; intro r1; apply mul_le_mul_left'
              exact pull_le_ideal_1 (pwr "g" r1) n q2 q3 eα ep2 "fwd1" ⟨"env", string2selfdelimitingString "pt1" ++ toString ({destination_name := "pt2", content := pwr "g" r1} : Message)⟩ hname2 rfl sOK_fwd1
          _ = ∑' r1, rnd r1 * ∑' a, rnd a * ∑' b, rnd b * ReturnsToExperiment (RIF (pwr "g" r1) (pwr "g" a) (pwr "g" b) 0 ⟨eα,ep2⟩) "env" ⟨"pt1", mc⟩ := by
              refine tsum_congr (fun r1 => congrArg _ (tsum_congr (fun a => congrArg _ (tsum_congr (fun b => congrArg _ ?_)))))
              exact (ReturnsToExperiment_of_peel 4 (peelI_0_pt1 (pwr "g" r1) (pwr "g" a) (pwr "g" b) eα ep2 hname2 mc)).symm
      by_cases h_pt2 : md = "pt2"
      · subst h_pt2
        calc cfgReturns (RID q2 q3 0 ⟨eα,ep2⟩) "env" ⟨"pt2", mc⟩ n
            ≤ cfgReturns (RID q2 q3 0 ⟨eα,ep2⟩) "pt2" ⟨"env", contentError⟩ n := by
              calc cfgReturns (RID q2 q3 0 ⟨eα,ep2⟩) "env" ⟨"pt2", mc⟩ n
                  ≤ cfgReturns (RID q2 q3 0 ⟨eα,ep2⟩) "env" ⟨"pt2", mc⟩ (n+3) := cfgReturns_le_add _ _ _ _ _
                _ = cfgReturns (RID q2 q3 0 ⟨eα,ep2⟩) "pt2" ⟨"env", contentError⟩ n := peelID_0_pt2 q2 q3 eα ep2 hname2 mc n
          _ ≤ ∑' r1, rnd r1 * ∑' a, rnd a * ∑' b, rnd b * ReturnsToExperiment (RIF (pwr "g" r1) (pwr "g" a) (pwr "g" b) 0 ⟨eα,ep2⟩) "pt2" ⟨"env", contentError⟩ :=
              ih n (Nat.lt_succ_self n) q2 q3 eα ep2 "pt2" ⟨"env", contentError⟩ hname2 rfl sOK_pt2
          _ = ∑' r1, rnd r1 * ∑' a, rnd a * ∑' b, rnd b * ReturnsToExperiment (RIF (pwr "g" r1) (pwr "g" a) (pwr "g" b) 0 ⟨eα,ep2⟩) "env" ⟨"pt2", mc⟩ := by
              refine tsum_congr (fun r1 => congrArg _ (tsum_congr (fun a => congrArg _ (tsum_congr (fun b => congrArg _ ?_)))))
              exact (ReturnsToExperiment_of_peel 3 (peelI_0_pt2 (pwr "g" r1) (pwr "g" a) (pwr "g" b) eα ep2 hname2 mc)).symm
      by_cases h_fwd1 : md = "fwd1"
      · subst h_fwd1
        calc cfgReturns (RID q2 q3 0 ⟨eα,ep2⟩) "env" ⟨"fwd1", mc⟩ n
            ≤ cfgReturns (RID q2 q3 0 ⟨eα,ep2⟩) "fwd1" ⟨"env", contentError⟩ n := by
              calc cfgReturns (RID q2 q3 0 ⟨eα,ep2⟩) "env" ⟨"fwd1", mc⟩ n
                  ≤ cfgReturns (RID q2 q3 0 ⟨eα,ep2⟩) "env" ⟨"fwd1", mc⟩ (n+3) := cfgReturns_le_add _ _ _ _ _
                _ = cfgReturns (RID q2 q3 0 ⟨eα,ep2⟩) "fwd1" ⟨"env", contentError⟩ n := peelID_0_fwd1 q2 q3 eα ep2 hname2 mc n
          _ ≤ ∑' r1, rnd r1 * ∑' a, rnd a * ∑' b, rnd b * ReturnsToExperiment (RIF (pwr "g" r1) (pwr "g" a) (pwr "g" b) 0 ⟨eα,ep2⟩) "fwd1" ⟨"env", contentError⟩ :=
              ih n (Nat.lt_succ_self n) q2 q3 eα ep2 "fwd1" ⟨"env", contentError⟩ hname2 rfl sOK_fwd1
          _ = ∑' r1, rnd r1 * ∑' a, rnd a * ∑' b, rnd b * ReturnsToExperiment (RIF (pwr "g" r1) (pwr "g" a) (pwr "g" b) 0 ⟨eα,ep2⟩) "env" ⟨"fwd1", mc⟩ := by
              refine tsum_congr (fun r1 => congrArg _ (tsum_congr (fun a => congrArg _ (tsum_congr (fun b => congrArg _ ?_)))))
              exact (ReturnsToExperiment_of_peel 3 (peelI_0_fwd1 (pwr "g" r1) (pwr "g" a) (pwr "g" b) eα ep2 hname2 mc)).symm
      by_cases h_fwd2 : md = "fwd2"
      · subst h_fwd2
        calc cfgReturns (RID q2 q3 0 ⟨eα,ep2⟩) "env" ⟨"fwd2", mc⟩ n
            ≤ cfgReturns (RID q2 q3 0 ⟨eα,ep2⟩) "fwd2" ⟨"env", contentError⟩ n := by
              calc cfgReturns (RID q2 q3 0 ⟨eα,ep2⟩) "env" ⟨"fwd2", mc⟩ n
                  ≤ cfgReturns (RID q2 q3 0 ⟨eα,ep2⟩) "env" ⟨"fwd2", mc⟩ (n+3) := cfgReturns_le_add _ _ _ _ _
                _ = cfgReturns (RID q2 q3 0 ⟨eα,ep2⟩) "fwd2" ⟨"env", contentError⟩ n := peelID_0_fwd2 q2 q3 eα ep2 hname2 mc n
          _ ≤ ∑' r1, rnd r1 * ∑' a, rnd a * ∑' b, rnd b * ReturnsToExperiment (RIF (pwr "g" r1) (pwr "g" a) (pwr "g" b) 0 ⟨eα,ep2⟩) "fwd2" ⟨"env", contentError⟩ :=
              ih n (Nat.lt_succ_self n) q2 q3 eα ep2 "fwd2" ⟨"env", contentError⟩ hname2 rfl sOK_fwd2
          _ = ∑' r1, rnd r1 * ∑' a, rnd a * ∑' b, rnd b * ReturnsToExperiment (RIF (pwr "g" r1) (pwr "g" a) (pwr "g" b) 0 ⟨eα,ep2⟩) "env" ⟨"fwd2", mc⟩ := by
              refine tsum_congr (fun r1 => congrArg _ (tsum_congr (fun a => congrArg _ (tsum_congr (fun b => congrArg _ ?_)))))
              exact (ReturnsToExperiment_of_peel 3 (peelI_0_fwd2 (pwr "g" r1) (pwr "g" a) (pwr "g" b) eα ep2 hname2 mc)).symm
      · calc cfgReturns (RID q2 q3 0 ⟨eα,ep2⟩) "env" ⟨md, mc⟩ n
            ≤ cfgReturns (RID q2 q3 0 ⟨eα,ep2⟩) "env" (destinationEnvMessage ⟨md, mc⟩) n := by
              calc cfgReturns (RID q2 q3 0 ⟨eα,ep2⟩) "env" ⟨md, mc⟩ n
                  ≤ cfgReturns (RID q2 q3 0 ⟨eα,ep2⟩) "env" ⟨md, mc⟩ (n+1) := cfgReturns_le_add _ _ _ _ _
                _ = cfgReturns (RID q2 q3 0 ⟨eα,ep2⟩) "env" (destinationEnvMessage ⟨md, mc⟩) n := peelID_other 0 q2 q3 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env n
          _ ≤ ∑' r1, rnd r1 * ∑' a, rnd a * ∑' b, rnd b * ReturnsToExperiment (RIF (pwr "g" r1) (pwr "g" a) (pwr "g" b) 0 ⟨eα,ep2⟩) "env" (destinationEnvMessage ⟨md, mc⟩) :=
              ih n (Nat.lt_succ_self n) q2 q3 eα ep2 "env" (destinationEnvMessage ⟨md, mc⟩) hname2 (by simp [destinationEnvMessage]) sOK_env
          _ = ∑' r1, rnd r1 * ∑' a, rnd a * ∑' b, rnd b * ReturnsToExperiment (RIF (pwr "g" r1) (pwr "g" a) (pwr "g" b) 0 ⟨eα,ep2⟩) "env" ⟨md, mc⟩ := by
              refine tsum_congr (fun r1 => congrArg _ (tsum_congr (fun a => congrArg _ (tsum_congr (fun b => congrArg _ ?_)))))
              exact (ReturnsToExperiment_of_peel 1 (peelI_other (pwr "g" r1) (pwr "g" a) (pwr "g" b) 0 eα ep2 hname2 md mc h_exp h_pt1 h_pt2 h_fwd1 h_fwd2 h_env)).symm

theorem route_stuck_idealD (q2 q3 : Nat) (eα : Type) (ep : Pin eα) (hne : ep.name ≠ "env")
    (m : Message) (hm : m.destination_name = "env") :
    Router.route (RID q2 q3 0 ⟨eα,ep⟩) "experiment" m
    = PMF.pure (RID q2 q3 0 ⟨eα,ep⟩, "experiment", destinationEnvMessage m) := by
  simp [RID, idealPinsRstD, idealWires, Router.route, Pin.invoke, changePinOfName, destinationEnvMessage, DummyPt1Pin, DummyPt2Pin, DummyFwd1Pin, DummyFwd2Pin, hm, hne, List.find?, List.map, bind, PMF.pure_bind]

theorem cfgReturns_stuck_idealD (q2 q3 : Nat) (eα : Type) (ep : Pin eα) (hne : ep.name ≠ "env") :
    ∀ (k : ℕ) (m : Message), m.destination_name = "env"
      → cfgReturns (RID q2 q3 0 ⟨eα,ep⟩) "experiment" m k = 0 := by
  intro k
  induction k with
  | zero => intro m hm; exact cfgReturns_zero_nexp _ _ _ (by rw [hm]; decide)
  | succ n ih =>
    intro m hm
    rw [cfgReturns_pure_step (by rw [hm]; decide) (route_stuck_idealD q2 q3 eα ep hne m hm)]
    exact ih _ (by simp [destinationEnvMessage])

theorem RTE_stuck_idealD (q2 q3 : Nat) (eα : Type) (ep : Pin eα) (hne : ep.name ≠ "env") :
    ReturnsToExperiment (RID q2 q3 0 ⟨eα,ep⟩) "experiment" startMessage = 0 := by
  rw [ReturnsToExperiment_eq_iSup]
  have h : ∀ k, cfgReturns (RID q2 q3 0 ⟨eα,ep⟩) "experiment" startMessage k = 0 :=
    fun k => cfgReturns_stuck_idealD q2 q3 eα ep hne k startMessage (by simp [startMessage])
  simp [h]

-- Ideal pull-out (one direction, as needed for decompI).
theorem idealPullout_le (env : SPin) :
    experimentIdeal env
    ≤ ∑' r1, rnd r1 * ∑' r2, rnd r2 * ∑' r3, rnd r3 * G env (pwr "g" r1) (pwr "g" r2) (pwr "g" r3) := by
  obtain ⟨eα, ep⟩ := env
  by_cases hn : ep.name = "env"
  · show ReturnsToExperiment (RID 0 0 0 ⟨eα,ep⟩) "experiment" startMessage
        ≤ ∑' r1, rnd r1 * ∑' r2, rnd r2 * ∑' r3, rnd r3
            * ReturnsToExperiment (RIF (pwr "g" r1) (pwr "g" r2) (pwr "g" r3) 0 ⟨eα,ep⟩) "experiment" startMessage
    rw [ReturnsToExperiment_eq_iSup (RID 0 0 0 ⟨eα,ep⟩)]
    exact iSup_le (fun k => pull_le_ideal_0 k 0 0 eα ep "experiment" startMessage hn
      (by simp [startMessage]) sOK_experiment)
  · show ReturnsToExperiment (RID 0 0 0 ⟨eα,ep⟩) "experiment" startMessage ≤ _
    rw [RTE_stuck_idealD 0 0 eα ep hn]
    exact zero_le'

theorem decompI (env : SPin) :
    experimentIdeal env ≤ ∑' t : String × String × String, distroI t * G env t.1 t.2.1 t.2.2 := by
  rw [sum_distroI_G]; exact idealPullout_le env

theorem decompR (env : SPin) :
    ∑' t : String × String × String, distroR t * G env t.1 t.2.1 t.2.2 ≤ experimentReal env := by
  rw [sum_distroR_G]; exact realPullout_ge env

-- ===========================================================================
-- The reduction (total-variation) bound.
-- ===========================================================================

theorem dist_probR_true (func : String × String × String → Bool) :
    (dist_probR func) true = ∑' t, distroR t * (if func t then (1 : ENNReal) else 0) := by
  unfold dist_probR
  rw [PMF.bind_apply]
  apply tsum_congr; intro t
  rw [PMF.pure_apply]
  by_cases h : func t <;> simp [h]

theorem dist_probI_true (func : String × String × String → Bool) :
    (dist_probI func) true = ∑' t, distroI t * (if func t then (1 : ENNReal) else 0) := by
  unfold dist_probI
  rw [PMF.bind_apply]
  apply tsum_congr; intro t
  rw [PMF.pure_apply]
  by_cases h : func t <;> simp [h]

-- general-index version of `ENNReal.tsum_sub`
theorem tsum_sub_gen {T : Type*} (F Gg : T → ENNReal) (hfin : ∑' t, Gg t ≠ ⊤)
    (hle : ∀ t, Gg t ≤ F t) :
    ∑' t, (F t - Gg t) = (∑' t, F t) - ∑' t, Gg t := by
  refine ENNReal.eq_sub_of_add_eq hfin ?_
  rw [← ENNReal.tsum_add]
  exact tsum_congr (fun t => tsub_add_cancel_of_le (hle t))

-- total variation is symmetric (both marginals sum to 1)
theorem tsum_tsub_symm :
    ∑' t : String × String × String, (distroI t - distroR t)
      = ∑' t : String × String × String, (distroR t - distroI t) := by
  have e1 : (∑' t : String × String × String, (distroI t - distroR t)) + 1
      = ∑' t, max (distroI t) (distroR t) := by
    rw [← distroR.tsum_coe, ← ENNReal.tsum_add]
    exact tsum_congr (fun t => tsub_add_eq_max)
  have e2 : (∑' t : String × String × String, (distroR t - distroI t)) + 1
      = ∑' t, max (distroI t) (distroR t) := by
    rw [← distroI.tsum_coe, ← ENNReal.tsum_add]
    refine tsum_congr (fun t => ?_)
    rw [tsub_add_eq_max, max_comm]
  have h := e1.trans e2.symm
  calc ∑' t : String × String × String, (distroI t - distroR t)
      = (∑' t, (distroI t - distroR t)) + 1 - 1 := (ENNReal.add_sub_cancel_right (by simp)).symm
    _ = (∑' t, (distroR t - distroI t)) + 1 - 1 := by rw [h]
    _ = ∑' t, (distroR t - distroI t) := ENNReal.add_sub_cancel_right (by simp)

open Classical in
noncomputable def distinguisher : String × String × String → Bool :=
  fun t => decide (distroI t < distroR t)

theorem tv_eq_dist_prob :
    ∑' t : String × String × String, (distroR t - distroI t) = dist_prob distinguisher := by
  have hlt : ∀ t, distinguisher t = true ↔ distroI t < distroR t := by
    intro t; rw [distinguisher]; exact decide_eq_true_iff
  unfold dist_prob
  rw [dist_probR_true, dist_probI_true]
  have hReq : ∀ t, distroR t * (if distinguisher t then (1 : ENNReal) else 0)
      = if distinguisher t then distroR t else 0 := by
    intro t; by_cases h : distinguisher t <;> simp [h]
  have hIeq : ∀ t, distroI t * (if distinguisher t then (1 : ENNReal) else 0)
      = if distinguisher t then distroI t else 0 := by
    intro t; by_cases h : distinguisher t <;> simp [h]
  simp_rw [hReq, hIeq]
  rw [← tsum_sub_gen (fun t => if distinguisher t then distroR t else 0)
        (fun t => if distinguisher t then distroI t else 0) ?_ ?_]
  · refine tsum_congr (fun t => ?_)
    by_cases h : distinguisher t = true
    · simp [h]
    · simp only [Bool.not_eq_true] at h
      have hle : distroR t ≤ distroI t := by
        rw [← not_lt]; intro hlt'
        rw [← hlt t] at hlt'
        rw [hlt'] at h
        exact absurd h (by decide)
      simp [h, tsub_eq_zero_of_le hle]
  · refine ne_of_lt (lt_of_le_of_lt ?_ ENNReal.one_lt_top)
    calc (∑' t, if distinguisher t then distroI t else 0) ≤ ∑' t, distroI t := by
          apply ENNReal.tsum_le_tsum; intro t; by_cases h : distinguisher t <;> simp [h]
      _ = 1 := distroI.tsum_coe
  · intro t; by_cases h : distinguisher t = true
    · simp only [h, if_true]; exact le_of_lt ((hlt t).mp h)
    · simp only [Bool.not_eq_true] at h; simp [h]

theorem tv_bound (env : SPin) :
    (∑' t : String × String × String, distroI t * G env t.1 t.2.1 t.2.2)
      - (∑' t : String × String × String, distroR t * G env t.1 t.2.1 t.2.2)
    ≤ least_upper_bound := by
  have hA : (∑' t : String × String × String, distroI t * G env t.1 t.2.1 t.2.2)
        - (∑' t : String × String × String, distroR t * G env t.1 t.2.1 t.2.2)
      ≤ ∑' t : String × String × String, (distroI t - distroR t) * G env t.1 t.2.1 t.2.2 := by
    rw [tsub_le_iff_right]
    calc (∑' t : String × String × String, distroI t * G env t.1 t.2.1 t.2.2)
        ≤ ∑' t : String × String × String,
            ((distroI t - distroR t) + distroR t) * G env t.1 t.2.1 t.2.2 := by
          apply ENNReal.tsum_le_tsum; intro t; exact mul_le_mul_right' le_tsub_add _
      _ = ∑' t : String × String × String,
            ((distroI t - distroR t) * G env t.1 t.2.1 t.2.2
              + distroR t * G env t.1 t.2.1 t.2.2) := by
          apply tsum_congr; intro t; rw [add_mul]
      _ = (∑' t : String × String × String, (distroI t - distroR t) * G env t.1 t.2.1 t.2.2)
            + ∑' t : String × String × String, distroR t * G env t.1 t.2.1 t.2.2 := ENNReal.tsum_add
  have hB : (∑' t : String × String × String, (distroI t - distroR t) * G env t.1 t.2.1 t.2.2)
      ≤ ∑' t : String × String × String, (distroI t - distroR t) := by
    apply ENNReal.tsum_le_tsum; intro t
    calc (distroI t - distroR t) * G env t.1 t.2.1 t.2.2
        ≤ (distroI t - distroR t) * 1 := mul_le_mul_left' (G_le_one env _ _ _) _
      _ = distroI t - distroR t := mul_one _
  have hC : (∑' t : String × String × String, (distroI t - distroR t)) ≤ least_upper_bound := by
    apply le_sInf
    intro x hx
    rw [tsum_tsub_symm, tv_eq_dist_prob]
    exact hx distinguisher
  exact (hA.trans hB).trans hC

theorem experimentIdeal_experimentReal :
  ∀ (env : SPin),
  experimentIdeal env - experimentReal env ≤ least_upper_bound := by
  intro env
  calc experimentIdeal env - experimentReal env
      ≤ (∑' t : String × String × String, distroI t * G env t.1 t.2.1 t.2.2)
          - (∑' t : String × String × String, distroR t * G env t.1 t.2.1 t.2.2) :=
        tsub_le_tsub (decompI env) (decompR env)
    _ ≤ least_upper_bound := tv_bound env
