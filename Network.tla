------------------------------ MODULE Network ------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC, Bags

\* Node the set of nodes in system
CONSTANTS Nodes


\* net {msg}
\* The network pool is a simple set holds all messages
VARIABLES net

\* dup_net Bags ([msg |-> Nat])
\* The duplicate network pool allows duplicate messages
VARIABLES dup_net

\* buf des -> {}
\* The Channel maps from des to a set of messages, receive of message can be out of order.
VARIABLES buf

\* chan src -> des -> {}
\* The channel maps from src to des's message pool
VARIABLES chan

\* fifo_chan src -> des -> <<>>
\* The fifo channel maps from src to des then to a sequence of messages, and consume from the head.
VARIABLES fifo_chan

vars == << net, dup_net, buf, chan, fifo_chan >>

Init == (* Global variables *)
        /\ net = {}
        /\ dup_net = EmptyBag
        /\ buf = [n \in Nodes |-> {}]
        /\ chan = [src \in Nodes |-> [des \in Nodes |-> {}]]
        /\ fifo_chan = [src \in Nodes |-> [des \in Nodes |-> <<>>]]


(***************************************************************************)
(* Utility functions                                                       *)
(***************************************************************************)
pick(set) == CHOOSE e \in set : TRUE

BagAdd(B, e) == B (+) [e |-> 1]

BagRemove(B, e) == B (-) [e |-> 1]


(***************************************************************************)
(* Network functions                                                       *)
(***************************************************************************)
net_send(msg) == /\ net' = net \union {msg}

net_multisend(msgs) == \A m \in msgs : net_send(m)

net_receive == /\ Cardinality(net) > 0
               /\ CHOOSE msg \in net : TRUE

net_drop(msg) == /\ msg \in net
                 /\ net' = net \ {msg}

buf_send(des, msg) == buf' = [buf EXCEPT ![des] = @ \union msg]

buf_multicast(group, msg) == \A des \in group : buf' = [buf EXCEPT ![des] = @ \union msg]

buf_discard(self, msg) == buf' = IF msg \in buf[self] THEN [buf EXCEPT ![self] = @ \ {msg}] ELSE buf

buf_reply(request, response) == buf_send(request.src, response) /\ buf_discard(response.src, request)

buf_receive(self) == /\ Cardinality(buf[self]) > 0
                     /\ LET msg == CHOOSE msg \in buf[self] : TRUE
                        IN  msg /\ buf_discard(self, msg)

dup_net_send(msg) == dup_net' = dup_net (+) [msg |-> 1]

dup_net_receive == /\ Cardinality(DOMAIN dup_net) > 0
                   /\ CHOOSE msg \in DOMAIN dup_net : TRUE

dup_net_drop(msg) == dup_net' = dup_net (-) [msg |-> 1]

dup_net_reply(request, response) == /\ dup_net_send(response)
                                    /\ dup_net_drop(request)

dup_net_multicast(group, msg) == \A des \in group : msg' = [msg EXCEPT !.des = des] /\ dup_net_send(msg)


chan_send(src, des, msg) == chan' = [chan EXCEPT ![src][des] = @ \union {msg}]

chan_discard(self, msg) == /\ \E src \in Nodes : msg \in chan[src][self]
                           /\ LET src == CHOOSE src \in Nodes : msg \in chan[src][self]
                              IN  chan' = [chan EXCEPT ![src][self] = @ \ {msg}]

chan_multicast(self, group, msg) == \A des \in group : chan_send(self, des, msg)

chan_receive(self) == /\ \E src \in Nodes : Cardinality(chan[src][self]) > 0
                      /\ LET src == CHOOSE src \in Nodes : Cardinality(chan[src][self]) > 0
                             msg == CHOOSE msg \in chan[src][self] : TRUE
                         IN  msg /\ chan' = [chan EXCEPT ![src][self] = @ \ {msg}]

-----------------------------------------------------------------------------

Next == /\ \/ chan_send(1, 1, 1)
           \/ chan_send(1, 2, 2)
           \/ chan_send(1, 2, 2)
           \/ chan_multicast(1, {1,2}, 999)
           \/ PrintT(chan_receive(2))
        /\ UNCHANGED << net, dup_net, buf, fifo_chan >>

Spec == Init /\ [][Next]_vars

Inv == Cardinality(net) <= 2

THEOREM Spec => []Inv

=============================================================================
\* Modification History
\* Last modified Tue Jul 18 15:53:49 PDT 2017 by ailidani
\* Created Mon Jul 17 11:22:35 PDT 2017 by ailidani
