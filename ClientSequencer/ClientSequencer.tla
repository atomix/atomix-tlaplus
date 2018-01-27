----------------------- MODULE ClientSequencer -----------------------

EXTENDS Naturals, FiniteSets, Sequences, Bags, TLC

\* Message types
CONSTANTS Response, Event

\* A bag of messages
VARIABLE messages

\* The total number of messages
VARIABLE messageCount

\* A sequence of all messaging variables
messageVars == <<messages, messageCount>>

\* Server variables
VARIABLES serverSequence, serverIndex, previousIndex

\* A sequence of all server variables
serverVars == <<serverSequence, serverIndex, previousIndex>>

\* Sequencer variables
VARIABLES responseSequence, responseIndex, eventIndex

\* The sequence of all ordered responses
VARIABLE responses

\* Variables used for queueing out of order responses and events
VARIABLE pendingResponses, pendingEvents

\* A sequence of all client variables
clientVars == <<responseSequence, responseIndex, eventIndex, responses, pendingResponses, pendingEvents>>

\* A sequence of all variables used in the spec
vars == <<messageVars, serverVars, clientVars>>

----

\* The type invariant verifies that the ordering of responses and events in the 'responses'
\* variable is sequential
TypeInvariant ==
    /\ \A r \in DOMAIN responses :
       IF r > 1 THEN
           LET
               current == responses[r]
               previous == responses[r-1]
           IN
               \/ /\ current.type = Event
                  /\ previous.type = Response
                  /\ current.eventIndex >= previous.index
               \/ /\ current.type = Response
                  /\ previous.type = Event
                  /\ current.index > previous.eventIndex
               \/ /\ current.type = Response
                  /\ previous.type = Response
                  /\ current.index > previous.index
       ELSE
           TRUE

----

\* Helper for adding a message to a bag of messages
WithMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = msgs[m] + 1]
    ELSE
        msgs @@ (m :> 1)

\* Helper for removing a message from a bag of messages
WithoutMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = msgs[m] - 1]
    ELSE
        msgs

\* Helper to send a message
Send(m) ==
    /\ messages' = WithMessage(m, messages)
    /\ messageCount' = messageCount + 1

\* Helper to discard a message
Discard(m) ==
    /\ messages' = WithoutMessage(m, messages)
    /\ messageCount' = messageCount + 1

\* Duplicates a message
Duplicate(m) ==
    /\ Send(m)
    /\ UNCHANGED <<clientVars, serverVars>>

\* Drops a message
Drop(m) == 
    /\ Discard(m)
    /\ UNCHANGED <<clientVars, serverVars>>

----

\* Sends a response to the client
\* The response will have a sequence number and index greater than all prior responses
SendResponse ==
    /\ Send([type |-> Response, index |-> serverIndex + 1, eventIndex |-> previousIndex, sequence |-> serverSequence])
    /\ serverSequence' = serverSequence + 1
    /\ serverIndex' = serverIndex + 1
    /\ UNCHANGED <<clientVars, previousIndex>>

\* Sends an event to the client
\* The sent event will have an index greater than all prior responses
SendEvent ==
    /\ previousIndex /= serverIndex
    /\ Send([type |-> Event, eventIndex |-> serverIndex, previousIndex |-> previousIndex])
    /\ previousIndex' = serverIndex
    /\ UNCHANGED <<clientVars, serverSequence, serverIndex>>

----

\* Accepts a response that has been received in order, adding it to the sequence of ordered responses
AcceptResponse(m) ==
    /\ responses' = responses \o <<m>>
    /\ responseSequence' = responseSequence + 1
    /\ responseIndex' = m.index
    /\ UNCHANGED <<pendingResponses>>

\* Queues a response for handling in order
QueueResponse(m) ==
    /\ pendingResponses' = pendingResponses \cup {m}
    /\ UNCHANGED <<responses, responseSequence, responseIndex>>

\* Handles a response from the cluster
HandleResponse(m) ==
    /\ \/ /\ m.sequence = responseSequence + 1
          /\ m.eventIndex = eventIndex
          /\ AcceptResponse(m)
       \/ QueueResponse(m)
    /\ UNCHANGED <<messageVars, serverVars, eventIndex, pendingEvents>>

\* Accepts an event that has been received in order, adding it to the sequence of ordered responses
AcceptEvent(m) ==
    /\ responses' = responses \o <<m>>
    /\ eventIndex' = m.eventIndex
    /\ UNCHANGED <<pendingEvents>>

\* Queues an event for handling in order
QueueEvent(m) ==
    /\ pendingEvents' = pendingEvents \cup {m}
    /\ UNCHANGED <<responses, eventIndex>>

\* Handles an event from the cluster
HandleEvent(m) ==
    /\ \/ /\ m.previousIndex = eventIndex
          /\ m.eventIndex = responseIndex
          /\ AcceptEvent(m)
       \/ QueueEvent(m)
    /\ UNCHANGED <<messageVars, serverVars, responseSequence, responseIndex, pendingResponses>>

\* Receives a message from the cluster
Receive(m) ==
  \/ /\ m.type = Response
     /\ HandleResponse(m)
  \/ /\ m.type = Event
     /\ HandleEvent(m)

\* Initial message variables
InitMessageVars ==
    /\ messages = [m \in {} |-> 0]
    /\ messageCount = 0

\* Initial server variables
InitServerVars ==
    /\ serverSequence = 1
    /\ serverIndex = 1
    /\ previousIndex = 0

\* Initial client variables
InitClientVars ==
    /\ responses = <<>>
    /\ pendingResponses = {}
    /\ pendingEvents = {}
    /\ responseSequence = 0
    /\ responseIndex = 0
    /\ eventIndex = 0

\* Initial state
Init ==
    /\ InitMessageVars
    /\ InitClientVars
    /\ InitServerVars

\* Next state predicate
Next ==
    \/ SendResponse
    \/ SendEvent
    \/ \E m \in DOMAIN messages : Receive(m)
    \/ \E m \in DOMAIN messages : Duplicate(m)
    \/ \E m \in DOMAIN messages : Drop(m)
    \/ \E m \in pendingResponses : HandleResponse(m)
    \/ \E m \in pendingEvents : HandleEvent(m)

\* The specification must start with an initial state and transition according to
\* the next state predicate
Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Wed Jan 24 21:18:32 PST 2018 by jordanhalterman
\* Created Wed Jan 24 10:02:25 PST 2018 by jordanhalterman
