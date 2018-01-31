------------------------------- MODULE Client -------------------------------

EXTENDS Messages, Server

\* The set of client IDs
CONSTANTS Client

VARIABLE sessions

VARIABLE clientRequest

clientVars == <<sessions, clientRequest>>

----

InitClientVars ==
    /\ sessions = [i \in Client |-> [id |-> Nil]]
    /\ clientRequest = 1

----

OpenSession(i, j) ==
    /\ state[j] = Leader
    /\ LET entry == [term   |-> currentTerm[j],
                     type   |-> OpenSessionEntry,
                     client |-> i]
       IN
           /\ log' = [log EXCEPT ![j] = Append(log[j], entry)]
           /\ clientRequest' = clientRequest + 1
    /\ UNCHANGED <<messages, serverVars, followerVars, candidateVars, leaderVars, commitIndex>>

CloseSession(i, j) ==
    /\ state[j] = Leader
    /\ LET entry == [term   |-> currentTerm[j],
                     type   |-> OpenSessionEntry,
                     client |-> i]
       IN
           /\ log' = [log EXCEPT ![j] = Append(log[j], entry)]
           /\ clientRequest' = clientRequest + 1
    /\ UNCHANGED <<messages, serverVars, followerVars, candidateVars, leaderVars, commitIndex>>

\* Leader i receives a client request to add v to the log.
ClientRequest(i, j) ==
    /\ state[j] = Leader
    /\ LET entry == [term  |-> currentTerm[j],
                     type  |-> CommandEntry,
                     value |-> clientRequest]
       IN
           /\ log' = [log EXCEPT ![j] = Append(log[j], entry)]
           /\ clientRequest' = clientRequest + 1
    /\ UNCHANGED <<messages, serverVars, followerVars, candidateVars, leaderVars, commitIndex>>

=============================================================================
\* Modification History
\* Last modified Tue Jan 30 16:35:28 PST 2018 by jordanhalterman
\* Created Tue Jan 30 15:04:21 PST 2018 by jordanhalterman
