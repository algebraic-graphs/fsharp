namespace Alga.FSharp

/// Abstract representation of vertices.
type Vertex = int

/// Adjacency list representation of a graph, mapping each vertex to its
/// list of successors.
type UntypedGraph = Vertex list array

/// An edge from the first vertex to the second.
type Edge = Vertex * Vertex


[<RequireQualifiedAccess>]
module Untyped =
    open System

    let vertices (g : UntypedGraph) : Vertex list =
        List.init g.Length id

    let edges (g : UntypedGraph) : Edge list =
        g |> vertices |> List.collect (fun v -> g.[v] |> List.map (fun v2 -> v, v2))

    /// Build a graph from a list of nodes uniquely identified by keys,
    /// with a list of keys of nodes this node should have edges to.
    /// The out-list may contain keys that don't correspond to
    /// nodes of the graph; they are ignored.
    let graphFromEdges (edges : ('node * 'key * 'key seq) seq) : (UntypedGraph * (Vertex -> ('node * 'key * 'key seq)) * ('key -> Vertex option)) =
        raise <| NotImplementedException "TODO: Implement me"

    /// A spanning forest of the part of the graph reachable from the listed
    /// vertices, obtained from a depth-first search of the graph starting at
    /// each of the listed vertices in order.
    let dfs (g : UntypedGraph) (vs : Vertex seq) : Vertex Forest =
        raise <| NotImplementedException "TODO: Implement me"

    /// A spanning forest of the graph, obtained from a depth-first search of
    /// the graph starting from each vertex in an unspecified order.
    let dff (g : UntypedGraph) : Vertex Forest =
        dfs g (vertices g)

    let rec postorder (t : 'a Tree) : 'a list =
        postorderF t.SubForest @ [t.RootLabel]

    and postorderF (ts : 'a Forest) : 'a list =
        ts |> List.collect postorder

    let postOrd (g : UntypedGraph) : Vertex list =
        g |> dff |> postorderF

    /// A topological sort of the graph.
    /// The order is partially specified by the condition that a vertex /i/
    /// precedes /j/ whenever /j/ is reachable from /i/ but not vice versa.
    let topSort (g : UntypedGraph) : Vertex list =
        g |> postOrd |> List.rev

    /// Build a graph from a list of edges.
    let buildG (size : int) (es : Edge list) : UntypedGraph =
        let g = Array.replicate size []
        es |> List.iter (fun (v1, v2) -> g.[v1] <- v2 :: g.[v1])
        g

    let reverseE (g : UntypedGraph) : Edge list =
        g |> edges |> List.map (fun (v, w) -> w, v)

    /// The graph obtained by reversing all edges.
    let transposeG (g : UntypedGraph) : UntypedGraph =
        buildG g.Length (reverseE g)

    /// The strongly connected components of a graph.
    let scc (g : UntypedGraph) : Vertex Forest =
        g |> transposeG |> postOrd |> List.rev |> dfs g
