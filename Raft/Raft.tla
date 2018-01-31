--------------------------------- MODULE Raft ---------------------------------
\* This is the formal specification for the Raft consensus algorithm.
\*
\* Copyright 2014 Diego Ongaro.
\* This work is licensed under the Creative Commons Attribution-4.0
\* International License https://creativecommons.org/licenses/by/4.0/

EXTENDS Naturals, FiniteSets, Sequences, TLC, Client, Server, Messages

----

\* All variables; used for stuttering (asserting state hasn't changed).
vars == <<messages, clientVars, serverVars, stateVars, followerVars, candidateVars, leaderVars, logVars>>

----

\* The network duplicates a message
DuplicateMessage(m) ==
    /\ Send(m)
    /\ UNCHANGED <<serverVars, stateVars, followerVars, candidateVars, leaderVars, logVars, clientVars>>

\* The network drops a message
DropMessage(m) ==
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, stateVars, followerVars, candidateVars, leaderVars, logVars, clientVars>>

----

Init ==
    /\ InitClientVars
    /\ InitServerVars
    /\ InitMessageVars

\* Defines how the variables may transition.
Next == \/ \E i \in Server : Restart(i)
           /\ UNCHANGED <<clientVars>>
        \/ \E i \in Server : TimeoutFollower(i)
           /\ UNCHANGED <<clientVars>>
        \/ \E i \in Server : TimeoutCandidate(i)
           /\ UNCHANGED <<clientVars>>
        \/ \E i, j \in Server : RequestPreVote(i, j)
           /\ UNCHANGED <<clientVars>>
        \/ \E i, j \in Server : RequestVote(i, j)
           /\ UNCHANGED <<clientVars>>
        \/ \E i \in Server : BecomeCandidate(i)
           /\ UNCHANGED <<clientVars>>
        \/ \E i \in Server : BecomeLeader(i)
           /\ UNCHANGED <<clientVars>>
        \/ \E i \in Client, j \in Server : OpenSession(i, j)
           /\ UNCHANGED <<serverVars, stateVars, followerVars, candidateVars, leaderVars, logVars>>
        \/ \E i \in Client, j \in Server : CloseSession(i, j)
           /\ UNCHANGED <<serverVars, stateVars, followerVars, candidateVars, leaderVars, logVars>>
        \/ \E i \in Client, j \in Server : ClientRequest(i, j)
           /\ UNCHANGED <<serverVars, stateVars, followerVars, candidateVars, leaderVars, logVars>>
        \/ \E i \in Server : AdvanceCommitIndex(i)
           /\ UNCHANGED <<clientVars>>
        \/ \E i \in Server : ApplyEntry(i)
           /\ UNCHANGED <<clientVars>>
        \/ \E i, j \in Server : AppendEntries(i, j)
           /\ UNCHANGED <<clientVars>>
        \/ \E m \in DOMAIN messages : Receive(m)
           /\ UNCHANGED <<clientVars>>
        \/ \E m \in DOMAIN messages : DuplicateMessage(m)
           /\ UNCHANGED <<clientVars>>
        \/ \E m \in DOMAIN messages : DropMessage(m)
           /\ UNCHANGED <<clientVars>>

Inv ==
    /\ \E s1, s2 \in Server :
           Len(log[s1]) > 0 /\ Len(log[s2]) > 0 => \E l1 \in DOMAIN log[s1], l2 \in DOMAIN log[s2] :
               l1 <= commitIndex[s1] /\ l2 <= commitIndex[s2] => log[s1][l1] = log[s2][l2]

\* The specification must start with the initial state and transition according
\* to Next.
Spec == Init /\ [][Next]_vars

===============================================================================
