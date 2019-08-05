------------------------------- MODULE Graphs -------------------------------
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Sequences
LOCAL INSTANCE Naturals
LOCAL INSTANCE TLC

LOCAL Last(seq) == seq[Len(seq)]

LOCAL EdgeSeq(graph) ==
  \* Without edge weights, any cycles in a sequence of edges is redundant
  \* So we can safely optimize out all sequences that visit the same node twice
  LET unique_sequences(m) ==
      {seq \in [1..m -> graph.node]: \A i, j \in 1..Len(seq): i /= j => seq[i] /= seq[j]}
  IN UNION {unique_sequences(m) : m \in 2..Cardinality(graph.node)} \* All edgeseqs need at least two nodes
LOCAL Pairs(Nodes) == Nodes \X Nodes

Graphs(Nodes) ==
  LET
    all_edges == [Pairs(Nodes) -> BOOLEAN]
    valid_edges ==
        {e \in all_edges: \A n \in Nodes: ~e[n, n]} \* No edges to self
  IN [
    node: {Nodes},
    edge: valid_edges
  ]

LOCAL ConnectedEdge(graph) ==
  LET F[<<x, y>> \in Pairs(graph.node)] ==
    \E path \in EdgeSeq(graph):
      /\ path[1] = x
      /\ Last(path) = y
      /\ \A i \in 1..Len(path)-1:
        graph.edge[path[i], path[i+1]]
  IN F

Undirected(graph) ==
  \A m, n \in graph.node: graph.edge[n, m] <=> graph.edge[m, n]

Acyclic(graph) ==
  LET edge == ConnectedEdge(graph)
  IN  \A n \in graph.node: ~edge[n, n]

WeaklyConnected(graph) ==
  LET edge == ConnectedEdge(graph)
  IN \A m, n \in graph.node: m /= n => edge[m, n] \/ edge[n, m]

\* To test this, remove the LOCAL and evaluate
LOCAL SanityCheck ==
  LET
    graphs == Graphs({1, 2, 3})
    AcyclicUndirected ==
      {g \in graphs: (\E p \in Pairs(g.node): g.edge[p]) /\ Acyclic(g) /\ Undirected(g)}
  IN
    CASE AcyclicUndirected /= {} -> Assert(FALSE,
      "All nontrivial undirected graphs should be cyclic, counterexample: "
      \o ToString(CHOOSE g \in AcyclicUndirected: TRUE))
    [] OTHER -> TRUE

=============================================================================
