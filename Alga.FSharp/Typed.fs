namespace Alga.FSharp

(*
Module     : Data.Graph.Typed
Copyright  : (c) Anton Lorenzen, Andrey Mokhov 2016-2018
License    : MIT (see the file LICENSE)
Maintainer : anfelor@posteo.de, andrey.mokhov@gmail.com
Stability  : unstable

__Alga__ is a library for algebraic construction and manipulation of graphs
in Haskell. See <https://github.com/snowleopard/alga-paper this paper> for the
motivation behind the library, the underlying theory, and implementation details.

This module provides primitives for interoperability between this library and
the "Data.Graph" module of the containers library. It is for internal use only
and may be removed without notice at any point.
*)

/// 'GraphKL' encapsulates King-Launchbury graphs, which are implemented in
/// the "Data.Graph" module of the @containers@ library.
type 'a GraphKL =
    {
        /// Array-based graph representation (King and Launchbury, 1995).
        ToGraphKL : UntypedGraph
        /// A mapping of "Data.Graph.Vertex" to vertices of type @a@.
        /// This is partial and may fail if the vertex is out of bounds.
        FromVertexKL : Vertex -> 'a
        /// A mapping from vertices of type @a@ to "Data.Graph.Vertex".
        /// Returns 'Nothing' if the argument is not in the graph.
        ToVertexKL : 'a -> Vertex option
    }

[<RequireQualifiedAccess>]
module Typed =

    /// Compute the /depth-first search/ forest of a graph.
    ///
    /// In the following we will use the helper function:
    ///
    /// @
    /// (%) :: (GraphKL Int -> a) -> AM.AdjacencyMap Int -> a
    /// a % g = a $ fromAdjacencyMap g
    /// @
    /// for greater clarity. (One could use an AdjacencyIntMap just as well)
    ///
    /// @
    /// 'Algebra.Graph.AdjacencyMap.forest' (dfsForest % 'Algebra.Graph.AdjacencyMap.edge' 1 1)           == 'AM.vertex' 1
    /// 'Algebra.Graph.AdjacencyMap.forest' (dfsForest % 'Algebra.Graph.AdjacencyMap.edge' 1 2)           == 'Algebra.Graph.AdjacencyMap.edge' 1 2
    /// 'Algebra.Graph.AdjacencyMap.forest' (dfsForest % 'Algebra.Graph.AdjacencyMap.edge' 2 1)           == 'AM.vertices' [1, 2]
    /// 'AM.isSubgraphOf' ('Algebra.Graph.AdjacencyMap.forest' $ dfsForest % x) x == True
    /// dfsForest % 'Algebra.Graph.AdjacencyMap.forest' (dfsForest % x)      == dfsForest % x
    /// dfsForest % 'AM.vertices' vs                 == map (\\v -> Node v []) ('Data.List.nub' $ 'Data.List.sort' vs)
    /// 'Algebra.Graph.AdjacencyMap.dfsForestFrom' ('Algebra.Graph.AdjacencyMap.vertexList' x) % x        == dfsForest % x
    /// dfsForest % (3 * (1 + 4) * (1 + 5))     == [ Node { rootLabel = 1
    ///                                                   , subForest = [ Node { rootLabel = 5
    ///                                                                        , subForest = [] }]}
    ///                                            , Node { rootLabel = 3
    ///                                                   , subForest = [ Node { rootLabel = 4
    ///                                                                        , subForest = [] }]}]
    /// @
    let dfsForest (g : 'a GraphKL) : 'a Forest =
        List.map (Tree.map g.FromVertexKL) (Untyped.dff g.ToGraphKL)

    /// Compute the /depth-first search/ forest of a graph, searching from each of
    /// the given vertices in order. Note that the resulting forest does not
    /// necessarily span the whole graph, as some vertices may be unreachable.
    ///
    /// @
    /// 'Algebra.Graph.AdjacencyMap.forest' (dfsForestFrom [1]    % 'Algebra.Graph.AdjacencyMap.edge' 1 1)       == 'AM.vertex' 1
    /// 'Algebra.Graph.AdjacencyMap.forest' (dfsForestFrom [1]    % 'Algebra.Graph.AdjacencyMap.edge' 1 2)       == 'Algebra.Graph.AdjacencyMap.edge' 1 2
    /// 'Algebra.Graph.AdjacencyMap.forest' (dfsForestFrom [2]    % 'Algebra.Graph.AdjacencyMap.edge' 1 2)       == 'AM.vertex' 2
    /// 'Algebra.Graph.AdjacencyMap.forest' (dfsForestFrom [3]    % 'Algebra.Graph.AdjacencyMap.edge' 1 2)       == 'AM.empty'
    /// 'Algebra.Graph.AdjacencyMap.forest' (dfsForestFrom [2, 1] % 'Algebra.Graph.AdjacencyMap.edge' 1 2)       == 'Algebra.Graph.AdjacencyMap.vertices' [1, 2]
    /// 'Algebra.Graph.AdjacencyMap.isSubgraphOf' ('Algebra.Graph.AdjacencyMap.forest' $ dfsForestFrom vs % x) x == True
    /// dfsForestFrom ('Algebra.Graph.AdjacencyMap.vertexList' x) % x               == 'dfsForest' % x
    /// dfsForestFrom vs               % 'Algebra.Graph.AdjacencyMap.vertices' vs   == map (\\v -> Node v []) ('Data.List.nub' vs)
    /// dfsForestFrom []               % x             == []
    /// dfsForestFrom [1, 4] % (3 * (1 + 4) * (1 + 5)) == [ Node { rootLabel = 1
    ///                                                          , subForest = [ Node { rootLabel = 5
    ///                                                                               , subForest = [] }
    ///                                                   , Node { rootLabel = 4
    ///                                                          , subForest = [] }]
    /// @
    let dfsForestFrom (vs : 'a seq) (g : 'a GraphKL) : 'a Forest =
        Untyped.dfs g.ToGraphKL (vs |> Seq.choose g.ToVertexKL) |> List.map (Tree.map g.FromVertexKL)

    /// Compute the list of vertices visited by the /depth-first search/ in a graph,
    /// when searching from each of the given vertices in order.
    ///
    /// @
    /// dfs [1]   % 'Algebra.Graph.AdjacencyMap.edge' 1 1                 == [1]
    /// dfs [1]   % 'Algebra.Graph.AdjacencyMap.edge' 1 2                 == [1,2]
    /// dfs [2]   % 'Algebra.Graph.AdjacencyMap.edge' 1 2                 == [2]
    /// dfs [3]   % 'Algebra.Graph.AdjacencyMap.edge' 1 2                 == []
    /// dfs [1,2] % 'Algebra.Graph.AdjacencyMap.edge' 1 2                 == [1,2]
    /// dfs [2,1] % 'Algebra.Graph.AdjacencyMap.edge' 1 2                 == [2,1]
    /// dfs []    % x                        == []
    /// dfs [1,4] % (3 * (1 + 4) * (1 + 5))  == [1, 5, 4]
    /// 'Algebra.Graph.AdjacencyMap.isSubgraphOf' ('Algebra.Graph.AdjacencyMap.vertices' $ dfs vs x) x == True
    /// @
    let dfs (vs : 'a seq) (g : 'a GraphKL) : 'a seq =
        g |> dfsForestFrom vs |> Seq.collect Tree.flatten

    /// Compute the /topological sort/ of a graph.
    /// Unlike the (Int)AdjacencyMap algorithm this returns
    /// a result even if the graph is cyclic.
    ///
    /// @
    /// topSort % (1 * 2 + 3 * 1) == [3,1,2]
    /// topSort % (1 * 2 + 2 * 1) == [1,2]
    /// @
    let topSort (g : 'a GraphKL) : 'a seq =
        Seq.map g.FromVertexKL (Untyped.topSort g.ToGraphKL)
