------------------------------ MODULE NetworkPluscal -------------------------

EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC, Bags, utility
CONSTANTS Nodes

ASSUME IsFiniteSet(Nodes)

(*
(* different types of network and functions *)
--algorithm network {

    variables net = {};
              dup_net = EmptyBag;
              buf = [des |-> {}];
              fifo_buf = [des |-> <<>>];
              chan = [from \in Nodes |-> [to \in Nodes |-> {}]];
              fifo_chan = [from \in Nodes |-> [to \in Nodes |-> <<>>]];

    macro buf_send(des, msg) {
        buf[des] := @ \cup {msg};
    }

    macro fifo_buf_multicast(group, msg) {
        buf := [d \in Nodes |-> IF d \in group THEN Append(chan[d], msg) ELSE chan[d]];
    }

    macro buf_discard(msg) {
        when msg \in chan[self];
        chan[self] := @ \ {msg};
    }

    macro buf_reply(request, response) {
        chan[request.src] := @ \union {response} || chan[self] := @ \ {request};
    }

    macro buf_receive() {
        with (m \in chan[self]) {
            msg := m;
            chan[self] := @ \ {m};
        }
    }

    macro fifo_buf_receive() {
        when Len(fifo_buf[self]) > 0;
        msg := Head(fifo_buf[self]);
        fifo_buf[self] := Tail(@);
    }


    \* send msg to one node
    macro fifo_send(to, msg) {
        fifo_chan[self][to] := Append(@, msg);
    }

    \* broadcast msg to all nodes including self
    macro fifo_broadcast(msg) {
        fifo_chan[self] := [to \in Nodes |-> Append(fifo_chan[self][to], msg)];
    }

    \* receive one msg from network
    macro fifo_receive() {
        with (from \in {j \in Nodes : Len(fifo_chan[j][self]) > 0}) {
            msg := Head(fifo_chan[from][self]);
            fifo_chan[from][self] := Tail(@);
        };
    }

    macro send(to, msg) {
        chan[self][to] := @ \union {msg}
    }

    macro broadcast(msg) {
        chan[self] := [to \in Node |-> chan[self][to] \union {msg}]
    }

    macro receive() {
\*        with (src \in Nodes : Cardinality(chan[src][self]) > 0) {
\*            CHOOSE m \in chan[src][self];
\*        }
        with (m \in chan[self]) {
            chan[self] := chan[self] \ {m};
        }
    }

    fair process (node \in Nodes)
    variable msg;
    {
        loop: while(TRUE) {
            send: send(self, <<"hello, world!">>);
            recv: fifo_receive();
        }
    }

}
*)

\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES fifo_chan, chan, pc, msg

vars == << fifo_chan, chan, pc, msg >>

ProcSet == (Nodes)

Init == (* Global variables *)
        /\ fifo_chan = [from \in Nodes |-> [to \in Nodes |-> <<>>]]
        /\ chan = [from \in Nodes |-> [to |-> {}]]
        (* Process node *)
        /\ msg = [self \in Nodes |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> "loop"]

loop(self) == /\ pc[self] = "loop"
              /\ pc' = [pc EXCEPT ![self] = "send"]
              /\ UNCHANGED << fifo_chan, chan, msg >>

send(self) == /\ pc[self] = "send"
              /\ chan' = [chan EXCEPT ![self][self] = @ \union {(<<"hello, world!">>)}]
              /\ pc' = [pc EXCEPT ![self] = "recv"]
              /\ UNCHANGED << fifo_chan, msg >>

recv(self) == /\ pc[self] = "recv"
              /\ \E from \in {j \in Nodes : Len(fifo_chan[j][self]) > 0}:
                   /\ msg' = [msg EXCEPT ![self] = Head(fifo_chan[from][self])]
                   /\ fifo_chan' = [fifo_chan EXCEPT ![from][self] = Tail(@)]
              /\ pc' = [pc EXCEPT ![self] = "loop"]
              /\ chan' = chan

node(self) == loop(self) \/ send(self) \/ recv(self)

Next == (\E self \in Nodes: node(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Nodes : WF_vars(node(self))

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Tue Jul 18 15:31:33 PDT 2017 by ailidani
\* Created Fri Mar 17 20:05:39 EDT 2017 by ailidani
