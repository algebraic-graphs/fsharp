namespace Alga.FSharp.Internal

/// An auxiliary data type for 'hasEdge': when searching for an edge, we can hit
/// its 'Tail', i.e. the source vertex, the whole 'Edge', or 'Miss' it entirely.
type Hit = Miss | Tail | Edge
