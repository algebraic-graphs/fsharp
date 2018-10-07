namespace Alga.FSharp.Internal

/// The /focus/ of a graph expression is a flattened represenentation of the
/// subgraph under focus, its context, as well as the list of all encountered
/// vertices. See 'Algebra.Graph.removeEdge' for a use-case example.
type 'a Focus =
    {
        Ok : bool     // True if focus on the specified subgraph is obtained.
        Is : 'a List  // Inputs into the focused subgraph.
        Os : 'a List  // Outputs out of the focused subgraph.
        Vs : 'a List  // All vertices (leaves) of the graph expression.
    }

/// An auxiliary data type for 'hasEdge': when searching for an edge, we can hit
/// its 'Tail', i.e. the source vertex, the whole 'Edge', or 'Miss' it entirely.
type Hit = Miss | Tail | Edge

[<RequireQualifiedAccess>]
module Focus =

    let focus ok is os vs = { Ok = ok ; Is = is ; Os = os ; Vs = vs }

    /// Focus on the empty graph.
    let emptyFocus<'a> : 'a Focus =
        focus false [] [] []

    /// Focus on the graph with a single vertex, given a predicate indicating
    /// whether the vertex is of interest.
    let vertexFocus (f : 'a -> bool) (x : 'a) : 'a Focus =
        focus (f x) [] [] [x]

    /// Overlay two foci.
    let overlayFoci (x : 'a Focus) (y : 'a Focus) : 'a Focus =
        focus (x.Ok || y.Ok) (x.Is @ y.Is) (x.Os @ y.Os) (x.Vs @ y.Vs)

    /// Connect two foci.
    let connectFoci (x : 'a Focus) (y : 'a Focus) : 'a Focus =
        let xs = if y.Ok then x.Vs else x.Is
        let ys = if x.Ok then y.Vs else y.Os
        focus (x.Ok || y.Ok) (xs @ y.Is) (x.Os @ ys) (x.Vs @ y.Vs)
