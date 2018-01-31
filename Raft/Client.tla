------------------------------- MODULE Client -------------------------------

EXTENDS Messages, Server

\* The set of client IDs
CONSTANTS Client

VARIABLE client

VARIABLE clientCommand

clientVars == <<client, clientCommand>>

----

InitClientVars ==
    /\ client = [i \in Client |-> [id |-> Nil]]
    /\ clientCommand = 1

----

OpenSession(c, s) ==
    /\ client[c].id = Nil
    /\ Send([mtype   |-> OpenSessionRequest,
             msource |-> c,
             mdest   |-> s])
    /\ UNCHANGED <<clientVars>>

CloseSession(c, s) ==
    /\ client[c].id # Nil
    /\ Send([mtype    |-> CloseSessionRequest,
             msession |-> client[c].id,
             msource  |-> c,
             mdest    |-> s])
    /\ UNCHANGED <<clientVars>>

ClientRequest(c, s) ==
    /\ client[c].id # Nil
    /\ Send([mtype |-> CommandRequest,
             msession |-> client[c].id,
             mcommand |-> clientCommand,
             msource |-> c,
             mdest |-> s])
    /\ clientCommand' = clientCommand + 1
    /\ UNCHANGED <<client>>

----

HandleOpenSessionResponse(c, m) ==
    /\ client' = [client EXCEPT ![c] = [id |-> m.msession]]
    /\ Discard(m)
    /\ UNCHANGED <<clientCommand>>

HandleCloseSessionResponse(c, m) ==
    /\ client' = [client EXCEPT ![c] = [id |-> Nil]]
    /\ Discard(m)
    /\ UNCHANGED <<clientCommand>>

HandleCommandResponse(c, m) ==
    /\ Discard(m)
    /\ UNCHANGED <<clientVars>>

----

ClientReceive(m) ==
    /\ LET c == m.mdest
       IN
           \/ /\ m.mtype = OpenSessionResponse
              /\ HandleOpenSessionResponse(c, m)
           \/ /\ m.mtype = CloseSessionResponse
              /\ HandleCloseSessionResponse(c, m)
           \/ /\ m.mtype = CommandResponse
              /\ HandleCommandResponse(c, m)

=============================================================================
\* Modification History
\* Last modified Tue Jan 30 22:18:13 PST 2018 by jordanhalterman
\* Created Tue Jan 30 15:04:21 PST 2018 by jordanhalterman
