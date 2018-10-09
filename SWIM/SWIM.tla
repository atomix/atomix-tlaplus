-------------------------------- MODULE SWIM --------------------------------

(*
This module contains a spec for Atomix' implementation of the SWIM protocol.
http://www.cs.cornell.edu/projects/Quicksilver/public_pdfs/SWIM.pdf

The SWIM protocol works by periodically probing peers to detect failures.
The Atomix implementation of the protocol propagates state changes to peers
using a gossip protocol. Members in the implementation can be in one of three
states at any given time: Alive, Suspect, or Dead. Time is tracked in this
implementation using logical clocks that are managed by each individual
member. A member can only increment its own logical clock (known as a term),
and within any given term the member can only be in a state once. Members
always transition from Alive->Suspect->Dead, and the term must be incremented
again to revert back to the Alive state. Member states transition back to
Alive by a Suspect or Dead member incrementing its term and refuting its
state.

While this spec does use probes, it does not request probes of a suspected
member from peers. Peer probes are a practical feature that does not add
value to the spec for purposes of model checking. A real implementation of
the protocol should use peer probes to avoid false positives.

The spec's invariant (Inv) asserts that no member can transition to the
same state multiple times in the same term, and state transitions always
progress from Alive to Suspect to Dead.

To perform model checking on the spec, define a set of numeric Members
and define the Nil, Dead, Suspect, and Alive constants as numeric values
of monotonically increasing values in that order. Additional constants
may be defined as desired.
*)

EXTENDS Naturals, FiniteSets, Sequences, Bags, TLC

\* The set of possible members
CONSTANT Member

\* Empty numeric value
CONSTANT Nil

\* Numeric member states
CONSTANTS Alive, Suspect, Dead

\* The values of member states must be sequential
ASSUME Alive > Suspect /\ Suspect > Dead

\* Message types
CONSTANTS GossipMessage, ProbeMessage, AckMessage

\* Member terms
VARIABLE term

\* Member lists
VARIABLE members

\* Pending updates
VARIABLE updates

\* History
VARIABLE history

\* A bag of records representing requests and responses sent from one server
\* to another. TLAPS doesn't support the Bags module, so this is a function
\* mapping Message to Nat.
VARIABLE messages

----

vars == <<term, members, updates, history, messages>>

----

InitMemberVars ==
    /\ term = [i \in Member |-> Nil]
    /\ members = [i \in Member |-> [j \in Member |-> [term |-> 0, state |-> Nil]]]
    /\ updates = [i \in Member |-> <<>>]
    /\ history = [i \in Member |-> [j \in Member |-> [k \in {} |-> <<>>]]]

InitMessageVars == messages = [m \in {} |-> 0]

----

\* Helper for Send and Reply. Given a message m and bag of messages, return a
\* new bag of messages with one more m in it.
WithMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = msgs[m] + 1]
    ELSE
        msgs @@ (m :> 1)

\* Helper for Discard and Reply. Given a message m and bag of messages, return
\* a new bag of messages with one less m in it.
WithoutMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = msgs[m] - 1]
    ELSE
        msgs

\* Add a message to the bag of messages.
Send(m) == messages' = WithMessage(m, messages)

\* Remove a message from the bag of messages. Used when a server is done
\* processing a message.
Discard(m) == messages' = WithoutMessage(m, messages)

\* Combination of Send and Discard
Reply(response, request) ==
    messages' = WithoutMessage(request, WithMessage(response, messages))

\* The network duplicates a message
DuplicateMessage(m) ==
    /\ messages[m] = 1
    /\ Send(m)
    /\ UNCHANGED <<term, members, updates, history>>

\* The network drops a message
DropMessage(m) ==
    /\ messages[m] > 0
    /\ Discard(m)
    /\ UNCHANGED <<term, members, updates, history>>

----

\* Returns a sequence with the head removed
Pop(q) == SubSeq(q, 2, Len(q))

\* Records an 'update' to gossipped by the given 'member'
RecordUpdate(member, update) ==
    /\ updates' = [updates EXCEPT ![member] = Append(updates[member], update)]

\* Removes the first update from the given 'member's updates
PopUpdate(member) ==
    /\ updates' = [updates EXCEPT ![member] = Pop(updates[member])]

\* Records a member state change on the given 'source' node
RecordHistory(source, dest, tm, state) ==
    IF tm \in DOMAIN history[source][dest] THEN
        history' = [history EXCEPT ![source][dest][tm] = Append(history[source][dest][tm], state)]
    ELSE
        history' = [history EXCEPT ![source] = history[source][dest] @@ (tm :> <<state>>)]

\* Updates the state of a peer on the given 'source' node
\* When the state of the 'dest' is updated, an update message is enqueued for gossip
\* and the state change is recorded in the 'source' node's history for model checking.
UpdateState(source, dest, tm, state) ==
    /\ IF dest \in DOMAIN members[source] THEN
           members' = [members EXCEPT ![source][dest] = [term |-> tm, state |-> state]]
       ELSE
           members' = [members EXCEPT ![source] = members[source] @@ (dest :> [term |-> tm, state |-> state])]
    /\ RecordUpdate(source, [id |-> dest, term |-> tm, state |-> state])
    /\ RecordHistory(source, dest, tm, state)

\* Sends a typed 'message' from the given 'source' to the given 'dest'
SendMessage(type, source, dest, message) ==
    Send([type |-> type, source |-> source, dest |-> dest, message |-> message])

\* Sends a probe 'message' from the given 'source' to the given 'dest'
SendProbe(source, dest, message) == SendMessage(ProbeMessage, source, dest, message)

\* Sends an ack 'message' from the given 'source' to the given 'dest'
SendAck(source, dest, message) == SendMessage(AckMessage, source, dest, message)

\* Sends a gossip 'message' from the given 'source' to the given 'dest'
SendGossip(source, dest, message) == SendMessage(GossipMessage, source, dest, message)

----

(*
Triggers a probe request to a peer
* 'source' is the source of the probe
* 'dest' is the destination to which to send the probe
*)
Probe(source, dest) ==
    /\ source # dest
    /\ term[source] # Nil
    /\ SendProbe(source, dest, members[source][dest])
    /\ UNCHANGED <<term, members, updates, history>>

(*
Handles a probe message from a peer
* 'source' is the source of the probe
* 'dest' is the destination receiving the probe
* 'message' is the probe message, containing the highest known destination state and term

If the received term is greater than the destination's term, update the destination's term
to 1 plus the received term. This can happen after a node leaves and rejoins the cluster.
If the destination is suspected by the source, increment the destination's term, enqueue
an update to be gossipped, and respond with the updated term.
If the destination's term is greater than the source's term, just send an ack.
*)
HandleProbe(source, dest, message) ==
    /\ term[dest] # Nil
    /\ \/ /\ message.term > term[dest]
          /\ term' = [term EXCEPT ![dest] = message.term + 1]
          /\ SendAck(dest, source, [term |-> term'[dest]])
       \/ /\ message.state = Suspect
          /\ term' = [term EXCEPT ![dest] = term[dest] + 1]
          /\ RecordUpdate(dest, [id |-> dest, term |-> term'[dest], state |-> Alive])
          /\ SendAck(dest, source, [term |-> term'[dest]])
       \/ /\ message.term <= term[dest]
          /\ SendAck(dest, source, [term |-> term[dest]])
          /\ UNCHANGED <<term>>
    /\ UNCHANGED <<members, updates, history>>
(*
Handles an ack message from a peer
* 'source' is the source of the ack
* 'dest' is the destination receiving the ack
* 'message' is the ack message

If the acknowledged message is greater than the term for the member on the destination
node, update the member's state and enqueue an update for gossip.
*)
HandleAck(source, dest, message) ==
    /\ \/ /\ message.term > members[dest][source].term
          /\ UpdateState(dest, source, message.term, Alive)
       \/ /\ message.term <= members[dest][source].term
          /\ UNCHANGED <<members, updates, history>>
    /\ UNCHANGED <<term, messages>>

(*
Handles a failed probe
* 'source' is the source of the probe
* 'dest' is the destination to which the probe was sent
* 'message' is the probe message

If the probe request matches the local term for the probe destination and the local
state for the destination is Alive, update the state to Suspect.
*)
HandleFail(source, dest, message) ==
    /\ \/ /\ dest \in DOMAIN members[source]
          /\ message.term = members[source][dest].term
          /\ members[source][dest].state = Alive
          /\ UpdateState(source, dest, message.term, Suspect)
    /\ UNCHANGED <<term, members, updates>>

(*
Expires a suspected peer
* 'source' is the node on which to expire the peer
* 'dest' is the peer to expire

If the destination's state is Suspect, change its state to Dead and enqueue a gossip
update to notify peers of the state change.
*)
Expire(source, dest) ==
    /\ source # dest
    /\ members[source][dest].state = Suspect
    /\ UpdateState(source, dest, members[source][dest].term, Dead)
    /\ UNCHANGED <<term>>

(*
Sends a gossip update to a peer
* 'source' is the source of the update
* 'dest' is the destination to which to send the update
*)
Gossip(source, dest) ==
    /\ source # dest
    /\ members[source][dest].state # Nil
    /\ Len(updates[source]) > 0
    /\ SendGossip(source, dest, updates[1])
    /\ PopUpdate(source)
    /\ UNCHANGED <<term, members, history>>

(*
Handles a gossip update
* 'source' is the source of the update
* 'dest' is the destination handling the update
* 'message' is the update message in the format with the updated member ID, term, and state

If the member is not present in the destination's members, add it to the members set.
If the term is greater than the destination's term for the gossipped member, update the member's
term and state on the destination node and enqueue the change for gossip.
If the term is equal to the destination's term for the member and the state is less than the
destination's state for the member, update the member's state on the destination node and
enqueue the change for gossip.
Record state changes in the history variable for model checking.
*)
HandleGossipUpdate(source, dest, message) ==
    /\ \/ /\ message.id \notin DOMAIN members[dest]
          /\ UpdateState(dest, message.id, message.term, message.state)
       \/ /\ message.id \in DOMAIN members[dest]
          /\ \/ /\ message.term > members[dest][message.id].term
             \/ /\ message.term = members[dest][message.id].term
                /\ message.state < members[dest][message.id].state
          /\ UpdateState(dest, message.id, message.term, message.state)
       \/ UNCHANGED <<members, updates, history>>
    /\ UNCHANGED <<term, messages>>

(*
Adds a member to the cluster
* 'id' is the identifier of the member to add

If the member is not present in the state history:
* Initialize the member's term to 1
* Initialize the member's states for all known members to term: 0, state: Dead to allow heartbeats
* Enqueue an update to notify peers of the member's existence
* Initialize the member's history
*)
AddMember(id) ==
    /\ term[id] = Nil
    /\ term' = [term EXCEPT ![id] = 1]
    /\ members' = [members EXCEPT ![id] = [i \in DOMAIN members |-> [term |-> 0, state |-> Dead]]]
    /\ history' = [history EXCEPT ![id] = [i \in {} |-> <<>>]]
    /\ UNCHANGED <<updates, messages>>

(*
Removes a member from the cluster
* 'id' is the identifier of the member to remove

Alter the domain of 'term', 'members', and 'updates' to remove the member's
volatile state. We retain only the in-flight messages and history for model checking.
*)
RemoveMember(id) ==
    /\ term[id] # Nil
    /\ term' = [term EXCEPT ![id] = Nil]
    /\ members' = [members EXCEPT ![id] = [j \in Member |-> [term |-> 0, state |-> Nil]]]
    /\ updates' = [updates EXCEPT ![id] = <<>>]
    /\ UNCHANGED <<history, messages>>

(*
Receives a message from the bag of messages
*)
ReceiveMessage(m) ==
    \/ /\ m.type = GossipMessage
       /\ HandleGossipUpdate(m.source, m.dest, m.message)
       /\ Discard(m)
    \/ /\ m.type = ProbeMessage
       /\ HandleProbe(m.source, m.dest, m.message)
       /\ Discard(m)
    \/ /\ m.type = AckMessage
       /\ HandleAck(m.source, m.dest, m.message)
       /\ Discard(m)
    \/ /\ m.type = ProbeMessage
       /\ HandleFail(m.source, m.dest, m.message)
       /\ Discard(m)

----

\* Initial state
Init ==
    /\ InitMessageVars
    /\ InitMemberVars

\* Next state predicate
Next ==
    \/ \E i, j \in Member : Probe(i, j)
    \/ \E i, j \in Member : Expire(i, j)
    \/ \E i, j \in Member : Gossip(i, j)
    \/ \E i \in Member : AddMember(i)
    \/ \E i \in Member : RemoveMember(i)
    \/ \E m \in DOMAIN messages : ReceiveMessage(m)
    \/ \E m \in DOMAIN messages : DuplicateMessage(m)
    \/ \E m \in DOMAIN messages : DropMessage(m)

\* Type invariant
Inv == \A i \in DOMAIN history :
           \A j \in DOMAIN history[i] :
               /\ ~\E k \in DOMAIN history[i][j] :
                      history[i][j][k+1] >= history[i][j][k]
               /\ Len(history[i][j]) <= 3

\* Spec
Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Mon Oct 08 17:17:17 PDT 2018 by jordanhalterman
\* Created Mon Oct 08 00:36:03 PDT 2018 by jordanhalterman
