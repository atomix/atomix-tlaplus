------------------------------- MODULE Messages -------------------------------

EXTENDS Naturals, TLC

\* A reserved value.
CONSTANTS Nil

\* A bag of records representing requests and responses sent from one server
\* to another. TLAPS doesn't support the Bags module, so this is a function
\* mapping Message to Nat.
VARIABLE messages

----

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

\* The network drops a message
DropMessage(m) ==
    /\ messages[m] > 0
    /\ Discard(m)

=============================================================================
\* Modification History
\* Last modified Wed Jan 31 20:55:09 PST 2018 by jordanhalterman
\* Created Tue Jan 30 15:04:21 PST 2018 by jordanhalterman
