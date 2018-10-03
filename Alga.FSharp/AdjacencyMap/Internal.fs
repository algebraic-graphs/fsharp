namespace rec Alga.FSharp.AdjacencyMap.Internal

open Alga.FSharp

(*
-- Module     : Algebra.Graph.AdjacencyMap.Internal
-- Copyright  : (c) Andrey Mokhov 2016-2018
-- License    : MIT (see the file LICENSE)
-- Maintainer : andrey.mokhov@gmail.com
-- Stability  : unstable
--
-- This module exposes the implementation of adjacency maps. The API is unstable
-- and unsafe, and is exposed only for documentation. You should use the
-- non-internal module "Algebra.Graph.AdjacencyMap" instead.

The 'AdjacencyMap' data type represents a graph by a map of vertices to
their adjacency sets. We define a 'Num' instance as a convenient notation for
working with graphs:

    > 0           == vertex 0
    > 1 + 2       == overlay (vertex 1) (vertex 2)
    > 1 * 2       == connect (vertex 1) (vertex 2)
    > 1 + 2 * 3   == overlay (vertex 1) (connect (vertex 2) (vertex 3))
    > 1 * (2 + 3) == connect (vertex 1) (overlay (vertex 2) (vertex 3))

The 'Show' instance is defined using basic graph construction primitives:

@show (empty     :: AdjacencyMap Int) == "empty"
show (1         :: AdjacencyMap Int) == "vertex 1"
show (1 + 2     :: AdjacencyMap Int) == "vertices [1,2]"
show (1 * 2     :: AdjacencyMap Int) == "edge 1 2"
show (1 * 2 * 3 :: AdjacencyMap Int) == "edges [(1,2),(1,3),(2,3)]"
show (1 * 2 + 3 :: AdjacencyMap Int) == "overlay (vertex 3) (edge 1 2)"@

The 'Eq' instance satisfies all axioms of algebraic graphs:

    * 'Algebra.Graph.AdjacencyMap.overlay' is commutative and associative:

        >       x + y == y + x
        > x + (y + z) == (x + y) + z

    * 'Algebra.Graph.AdjacencyMap.connect' is associative and has
    'Algebra.Graph.AdjacencyMap.empty' as the identity:

        >   x * empty == x
        >   empty * x == x
        > x * (y * z) == (x * y) * z

    * 'Algebra.Graph.AdjacencyMap.connect' distributes over
    'Algebra.Graph.AdjacencyMap.overlay':

        > x * (y + z) == x * y + x * z
        > (x + y) * z == x * z + y * z

    * 'Algebra.Graph.AdjacencyMap.connect' can be decomposed:

        > x * y * z == x * y + x * z + y * z

The following useful theorems can be proved from the above set of axioms.

    * 'Algebra.Graph.AdjacencyMap.overlay' has 'Algebra.Graph.AdjacencyMap.empty'
    as the identity and is idempotent:

        >   x + empty == x
        >   empty + x == x
        >       x + x == x

    * Absorption and saturation of 'Algebra.Graph.AdjacencyMap.connect':

        > x * y + x + y == x * y
        >     x * x * x == x * x

When specifying the time and memory complexity of graph algorithms, /n/ and /m/
will denote the number of vertices and edges in the graph, respectively.
*)

/// The /adjacency map/ of the graph: each vertex is associated with a set
/// of its direct successors. Complexity: /O(1)/ time and memory.
///
/// @
/// adjacencyMap 'empty'      == Map.'Map.empty'
/// adjacencyMap ('vertex' x) == Map.'Map.singleton' x Set.'Set.empty'
/// adjacencyMap ('Algebra.Graph.AdjacencyMap.edge' 1 1) == Map.'Map.singleton' 1 (Set.'Set.singleton' 1)
/// adjacencyMap ('Algebra.Graph.AdjacencyMap.edge' 1 2) == Map.'Map.fromList' [(1,Set.'Set.singleton' 2), (2,Set.'Set.empty')]
/// @
type AdjacencyMap<'a when 'a : comparison> = AdjacencyMap of Map<'a, 'a Set>
with

    static member (+) (x : 'a AdjacencyMap, y : 'a AdjacencyMap) = AdjacencyMap.overlay x y
    static member (*) (x : 'a AdjacencyMap, y : 'a AdjacencyMap) = AdjacencyMap.connect x y

    override this.ToString () =

        let (AdjacencyMap m) = this
        let vs = m |> Map.toSeq |> Seq.map fst |> Seq.sort |> List.ofSeq
        let es = m |> AdjacencyMap.internalEdgeList |> List.ofSeq

        let vshow =
            function
            | [x] -> sprintf "vertex %A" x
            | xs -> sprintf "vertices %A" xs

        let eshow =
            function
            | [x, y] -> sprintf "edge %A %A" x y
            | xs -> sprintf "edges %A" xs

        let used = m |> AdjacencyMap.referredToVertexSet |> Set.toSeq |> Seq.sort |> List.ofSeq

        if vs |> Seq.isEmpty then
            "empty"
        else if es |> Seq.isEmpty then
            vshow vs
        else if vs = used then
            eshow es
        else
            sprintf "overlay (%s) (%s)"
                (vshow (Set.difference (vs |> Set.ofSeq) (used |> Set.ofSeq) |> Set.toList))
                (eshow es)

[<RequireQualifiedAccess>]
module AdjacencyMap =

    //-- | Construct the /empty graph/.
    //-- Complexity: /O(1)/ time and memory.
    //--
    //-- @
    //-- 'Algebra.Graph.AdjacencyMap.isEmpty'     empty == True
    //-- 'Algebra.Graph.AdjacencyMap.hasVertex' x empty == False
    //-- 'Algebra.Graph.AdjacencyMap.vertexCount' empty == 0
    //-- 'Algebra.Graph.AdjacencyMap.edgeCount'   empty == 0
    //-- @
    let empty : 'a AdjacencyMap =
        AdjacencyMap Map.empty

    /// Construct the graph comprising /a single isolated vertex/.
    /// Complexity: /O(1)/ time and memory.
    ///
    /// @
    /// 'Algebra.Graph.AdjacencyMap.isEmpty'     (vertex x) == False
    /// 'Algebra.Graph.AdjacencyMap.hasVertex' x (vertex x) == True
    /// 'Algebra.Graph.AdjacencyMap.vertexCount' (vertex x) == 1
    /// 'Algebra.Graph.AdjacencyMap.edgeCount'   (vertex x) == 0
    /// @
    let vertex (x : 'a) : 'a AdjacencyMap =
        Map.empty |> Map.add x Set.empty |> AdjacencyMap

    /// /Overlay/ two graphs. This is a commutative, associative and idempotent
    /// operation with the identity 'empty'.
    /// Complexity: /O((n + m) * log(n))/ time and /O(n + m)/ memory.
    ///
    /// @
    /// 'Algebra.Graph.AdjacencyMap.isEmpty'     (overlay x y) == 'Algebra.Graph.AdjacencyMap.isEmpty'   x   && 'Algebra.Graph.AdjacencyMap.isEmpty'   y
    /// 'Algebra.Graph.AdjacencyMap.hasVertex' z (overlay x y) == 'Algebra.Graph.AdjacencyMap.hasVertex' z x || 'Algebra.Graph.AdjacencyMap.hasVertex' z y
    /// 'Algebra.Graph.AdjacencyMap.vertexCount' (overlay x y) >= 'Algebra.Graph.AdjacencyMap.vertexCount' x
    /// 'Algebra.Graph.AdjacencyMap.vertexCount' (overlay x y) <= 'Algebra.Graph.AdjacencyMap.vertexCount' x + 'Algebra.Graph.AdjacencyMap.vertexCount' y
    /// 'Algebra.Graph.AdjacencyMap.edgeCount'   (overlay x y) >= 'Algebra.Graph.AdjacencyMap.edgeCount' x
    /// 'Algebra.Graph.AdjacencyMap.edgeCount'   (overlay x y) <= 'Algebra.Graph.AdjacencyMap.edgeCount' x   + 'Algebra.Graph.AdjacencyMap.edgeCount' y
    /// 'Algebra.Graph.AdjacencyMap.vertexCount' (overlay 1 2) == 2
    /// 'Algebra.Graph.AdjacencyMap.edgeCount'   (overlay 1 2) == 0
    /// @
    let overlay (AdjacencyMap x) (AdjacencyMap y) : 'a AdjacencyMap =

        Map.unionWith Set.union x y |> AdjacencyMap

    /// /Connect/ two graphs. This is an associative operation with the identity
    /// 'empty', which distributes over 'overlay' and obeys the decomposition axiom.
    /// Complexity: /O((n + m) * log(n))/ time and /O(n + m)/ memory. Note that the
    /// number of edges in the resulting graph is quadratic with respect to the number
    /// of vertices of the arguments: /m = O(m1 + m2 + n1 * n2)/.
    ///
    /// @
    /// 'isEmpty'     (connect x y) == 'isEmpty'   x   && 'Algebra.Graph.AdjacencyMap.isEmpty'   y
    /// 'hasVertex' z (connect x y) == 'hasVertex' z x || 'Algebra.Graph.AdjacencyMap.hasVertex' z y
    /// 'vertexCount' (connect x y) >= 'vertexCount' x
    /// 'vertexCount' (connect x y) <= 'vertexCount' x + 'Algebra.Graph.AdjacencyMap.vertexCount' y
    /// 'edgeCount'   (connect x y) >= 'edgeCount' x
    /// 'edgeCount'   (connect x y) >= 'edgeCount' y
    /// 'edgeCount'   (connect x y) >= 'vertexCount' x * 'Algebra.Graph.AdjacencyMap.vertexCount' y
    /// 'edgeCount'   (connect x y) <= 'vertexCount' x * 'Algebra.Graph.AdjacencyMap.vertexCount' y + 'Algebra.Graph.AdjacencyMap.edgeCount' x + 'Algebra.Graph.AdjacencyMap.edgeCount' y
    /// 'vertexCount' (connect 1 2) == 2
    /// 'edgeCount'   (connect 1 2) == 1
    /// @
    let connect (AdjacencyMap x) (AdjacencyMap y) : 'a AdjacencyMap =
        let fromSet f s = s |> Seq.map (fun k -> k, f k) |> Map.ofSeq
        Map.unionsWith Set.union [ x ; y ; fromSet (fun _ -> Map.keysSet y) (Map.keysSet x) ] |> AdjacencyMap

    /// Construct a graph from a list of adjacency sets.
    /// Complexity: /O((n + m) * log(n))/ time and /O(n + m)/ memory.
    ///
    /// @
    /// fromAdjacencySets []                                        == 'Algebra.Graph.AdjacencyMap.empty'
    /// fromAdjacencySets [(x, Set.'Set.empty')]                          == 'Algebra.Graph.AdjacencyMap.vertex' x
    /// fromAdjacencySets [(x, Set.'Set.singleton' y)]                    == 'Algebra.Graph.AdjacencyMap.edge' x y
    /// fromAdjacencySets . map (fmap Set.'Set.fromList') . 'Algebra.Graph.AdjacencyMap.adjacencyList' == id
    /// 'Algebra.Graph.AdjacencyMap.overlay' (fromAdjacencySets xs) (fromAdjacencySets ys)       == fromAdjacencySets (xs ++ ys)
    /// @
    //fromAdjacencySets :: Ord a => [(a, Set a)] -> AdjacencyMap a
    let fromAdjacencySets (ss : ('a * 'a Set) seq) : 'a AdjacencyMap =
        let vs = ss |> Seq.map snd |> Set.unionMany |> Seq.map (fun k -> k, Set.empty) |> Map.ofSeq
        let es = ss |> Map.ofSeq
        Map.unionWith Set.union vs es |> AdjacencyMap

    /// Check if the internal graph representation is consistent, i.e. that all
    /// edges refer to existing vertices. It should be impossible to create an
    /// inconsistent adjacency map, and we use this function in testing.
    /// /Note: this function is for internal use only/.
    ///
    /// @
    /// consistent 'Algebra.Graph.AdjacencyMap.empty'         == True
    /// consistent ('Algebra.Graph.AdjacencyMap.vertex' x)    == True
    /// consistent ('Algebra.Graph.AdjacencyMap.overlay' x y) == True
    /// consistent ('Algebra.Graph.AdjacencyMap.connect' x y) == True
    /// consistent ('Algebra.Graph.AdjacencyMap.edge' x y)    == True
    /// consistent ('Algebra.Graph.AdjacencyMap.edges' xs)    == True
    /// consistent ('Algebra.Graph.AdjacencyMap.stars' xs)    == True
    /// @
    let consistent (AdjacencyMap m) : bool =
        Set.isSubset (referredToVertexSet m) (Map.keysSet m)

    /// The set of vertices that are referred to by the edges
    //referredToVertexSet :: Ord a => Map a (Set a) -> Set a
    let referredToVertexSet (m : Map<'a, 'a Set>) : 'a Set =
        let s = m |> internalEdgeList
        Seq.append (s |> Seq.map fst) (s |> Seq.map snd) |> Set.ofSeq

    /// The list of edges in adjacency map
    let internalEdgeList (m : Map<'a, 'a Set>) : ('a * 'a) seq =
        seq {
            for (x, ys) in m |> Map.toSeq |> Seq.sort do
                for y in ys |> Set.toSeq |> Seq.sort do
                    yield x, y
        }
