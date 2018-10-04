namespace Alga.FSharp.Internal

open Alga.FSharp
open Alga.FSharp.AdjacencyMap.Internal

(*
Module     : Algebra.Graph.AdjacencyMap
Copyright  : (c) Andrey Mokhov 2016-2018
License    : MIT (see the file LICENSE)
Maintainer : andrey.mokhov@gmail.com
Stability  : experimental

__Alga__ is a library for algebraic construction and manipulation of graphs
in Haskell. See <https://github.com/snowleopard/alga-paper this paper> for the
motivation behind the library, the underlying theory, and implementation details.

This module defines the 'AdjacencyMap' data type, as well as associated
operations and algorithms. 'AdjacencyMap' is an instance of the 'C.Graph' type
class, which can be used for polymorphic graph construction and manipulation.
"Algebra.Graph.AdjacencyIntMap" defines adjacency maps specialised to graphs
with @Int@ vertices.
*)

[<RequireQualifiedAccess>]
module AdjacencyMap =

    /// Construct the graph comprising /a single edge/.
    /// Complexity: /O(1)/ time, memory.
    ///
    /// @
    /// edge x y               == 'connect' ('vertex' x) ('vertex' y)
    /// 'hasEdge' x y (edge x y) == True
    /// 'edgeCount'   (edge x y) == 1
    /// 'vertexCount' (edge 1 1) == 1
    /// 'vertexCount' (edge 1 2) == 2
    /// @
    let edge (x : 'a) (y : 'a) : 'a AdjacencyMap =
        if x = y then
            Map.singleton x (y |> Set.singleton) |> AdjacencyMap
        else
            [(x, Set.singleton y) ; (y, Set.empty)] |> Map.ofSeq |> AdjacencyMap

    /// Construct the graph comprising a given list of isolated vertices.
    /// Complexity: /O(L * log(L))/ time and /O(L)/ memory, where /L/ is the length
    /// of the given list.
    ///
    /// @
    /// vertices []            == 'empty'
    /// vertices [x]           == 'vertex' x
    /// 'hasVertex' x . vertices == 'elem' x
    /// 'vertexCount' . vertices == 'length' . 'Data.List.nub'
    /// 'vertexSet'   . vertices == Set.'Set.fromList'
    /// @
    let vertices (vs : 'a seq) : 'a AdjacencyMap =
        vs |> Seq.map (fun v -> v, Set.empty) |> Map.ofSeq |> AdjacencyMap

    /// Construct the graph from a list of edges.
    /// Complexity: /O((n + m) * log(n))/ time and /O(n + m)/ memory.
    ///
    /// @
    /// edges []          == 'empty'
    /// edges [(x,y)]     == 'edge' x y
    /// 'edgeCount' . edges == 'length' . 'Data.List.nub'
    /// 'edgeList' . edges  == 'Data.List.nub' . 'Data.List.sort'
    /// @
    let edges (es : ('a * 'a) seq) : 'a AdjacencyMap =
        es |> Seq.map (fun (v1, v2) -> v1, Set.singleton v2) |> AdjacencyMap.fromAdjacencySets

    /// Overlay a given list of graphs.
    /// Complexity: /O((n + m) * log(n))/ time and /O(n + m)/ memory.
    ///
    /// @
    /// overlays []        == 'empty'
    /// overlays [x]       == x
    /// overlays [x,y]     == 'overlay' x y
    /// overlays           == 'foldr' 'overlay' 'empty'
    /// 'isEmpty' . overlays == 'all' 'isEmpty'
    /// @
    let overlays (ams : 'a AdjacencyMap seq) : 'a AdjacencyMap =
        ams |> Seq.map (fun (AdjacencyMap m) -> m) |> Map.unionsWith Set.union |> AdjacencyMap

    /// Connect a given list of graphs.
    /// Complexity: /O((n + m) * log(n))/ time and /O(n + m)/ memory.
    ///
    /// @
    /// connects []        == 'empty'
    /// connects [x]       == x
    /// connects [x,y]     == 'connect' x y
    /// connects           == 'foldr' 'connect' 'empty'
    /// 'isEmpty' . connects == 'all' 'isEmpty'
    /// @
    let connects (ams : 'a AdjacencyMap seq) : 'a AdjacencyMap =
        Seq.fold AdjacencyMap.connect AdjacencyMap.empty ams

    /// The 'isSubgraphOf' function takes two graphs and returns 'True' if the
    /// first graph is a /subgraph/ of the second.
    /// Complexity: /O((n + m) * log(n))/ time.
    ///
    /// @
    /// isSubgraphOf 'empty'         x             == True
    /// isSubgraphOf ('vertex' x)    'empty'         == False
    /// isSubgraphOf x             ('overlay' x y) == True
    /// isSubgraphOf ('overlay' x y) ('connect' x y) == True
    /// isSubgraphOf ('path' xs)     ('circuit' xs)  == True
    /// @
    let isSubgraphOf (AdjacencyMap x) (AdjacencyMap y) : bool =
        Map.isSubmapOfBy Set.isSubset x y

    /// Check if a graph is empty.
    /// Complexity: /O(1)/ time.
    ///
    /// @
    /// isEmpty 'empty'                       == True
    /// isEmpty ('overlay' 'empty' 'empty')       == True
    /// isEmpty ('vertex' x)                  == False
    /// isEmpty ('removeVertex' x $ 'vertex' x) == True
    /// isEmpty ('removeEdge' x y $ 'edge' x y) == False
    /// @
    let isEmpty (AdjacencyMap m) : bool =
        m |> Map.isEmpty

    /// Check if a graph contains a given vertex.
    /// Complexity: /O(log(n))/ time.
    ///
    /// @
    /// hasVertex x 'empty'            == False
    /// hasVertex x ('vertex' x)       == True
    /// hasVertex 1 ('vertex' 2)       == False
    /// hasVertex x . 'removeVertex' x == const False
    /// @
    let hasVertex (v : 'a) (AdjacencyMap m) : bool =
        Map.containsKey v m

    /// Check if a graph contains a given edge.
    /// Complexity: /O(log(n))/ time.
    ///
    /// @
    /// hasEdge x y 'empty'            == False
    /// hasEdge x y ('vertex' z)       == False
    /// hasEdge x y ('edge' x y)       == True
    /// hasEdge x y . 'removeEdge' x y == const False
    /// hasEdge x y                  == 'elem' (x,y) . 'edgeList'
    /// @
    let hasEdge (u : 'a) (v : 'a) (AdjacencyMap m) : bool =
        match Map.tryFind u m with
        | None -> false
        | Some vs -> Set.contains v vs

    /// The number of vertices in a graph.
    /// Complexity: /O(1)/ time.
    ///
    /// @
    /// vertexCount 'empty'      == 0
    /// vertexCount ('vertex' x) == 1
    /// vertexCount            == 'length' . 'vertexList'
    /// @
    let vertexCount (AdjacencyMap m) : int =
        Map.count m

    /// The number of edges in a graph.
    /// Complexity: /O(n)/ time.
    ///
    /// @
    /// edgeCount 'empty'      == 0
    /// edgeCount ('vertex' x) == 0
    /// edgeCount ('edge' x y) == 1
    /// edgeCount            == 'length' . 'edgeList'
    /// @
    //edgeCount :: AdjacencyMap a -> Int
    //edgeCount = getSum . foldMap (Sum . Set.size) . adjacencyMap
    let edgeCount (AdjacencyMap m) : int =
        m |> Map.fold (fun s k v -> s + (v |> Set.count)) 0

    /// The sorted list of vertices of a given graph.
    /// Complexity: /O(n)/ time and memory.
    ///
    /// @
    /// vertexList 'empty'      == []
    /// vertexList ('vertex' x) == [x]
    /// vertexList . 'vertices' == 'Data.List.nub' . 'Data.List.sort'
    /// @
    //vertexList :: AdjacencyMap a -> [a]
    //vertexList = Map.keys . adjacencyMap
    let vertexList (AdjacencyMap m) : 'a seq =
        m |> Map.keys

    /// The sorted list of edges of a graph.
    /// Complexity: /O(n + m)/ time and /O(m)/ memory.
    ///
    /// @
    /// edgeList 'empty'          == []
    /// edgeList ('vertex' x)     == []
    /// edgeList ('edge' x y)     == [(x,y)]
    /// edgeList ('star' 2 [3,1]) == [(2,1), (2,3)]
    /// edgeList . 'edges'        == 'Data.List.nub' . 'Data.List.sort'
    /// edgeList . 'transpose'    == 'Data.List.sort' . map 'Data.Tuple.swap' . edgeList
    /// @
    let edgeList (AdjacencyMap m) : ('a * 'a) seq =
        seq {
            for (x, ys) in m |> Map.toSeq do
                for y in ys do
                    yield x, y
        }

    /// The set of vertices of a given graph.
    /// Complexity: /O(n)/ time and memory.
    ///
    /// @
    /// vertexSet 'empty'      == Set.'Set.empty'
    /// vertexSet . 'vertex'   == Set.'Set.singleton'
    /// vertexSet . 'vertices' == Set.'Set.fromList'
    /// vertexSet . 'clique'   == Set.'Set.fromList'
    /// @
    //vertexSet :: AdjacencyMap a -> Set a
    //vertexSet = Map.keysSet . adjacencyMap
    let vertexSet (AdjacencyMap m) : 'a Set =
        m |> Map.keysSet

    /// The set of edges of a given graph.
    /// Complexity: /O((n + m) * log(m))/ time and /O(m)/ memory.
    ///
    /// @
    /// edgeSet 'empty'      == Set.'Set.empty'
    /// edgeSet ('vertex' x) == Set.'Set.empty'
    /// edgeSet ('edge' x y) == Set.'Set.singleton' (x,y)
    /// edgeSet . 'edges'    == Set.'Set.fromList'
    /// @
    let edgeSet (am : 'a AdjacencyMap) : ('a * 'a) Set =
        am |> edgeList |> Set.ofSeq

    /// The sorted /adjacency list/ of a graph.
    /// Complexity: /O(n + m)/ time and /O(m)/ memory.
    ///
    /// @
    /// adjacencyList 'empty'          == []
    /// adjacencyList ('vertex' x)     == [(x, [])]
    /// adjacencyList ('edge' 1 2)     == [(1, [2]), (2, [])]
    /// adjacencyList ('star' 2 [3,1]) == [(1, []), (2, [1,3]), (3, [])]
    /// 'stars' . adjacencyList        == id
    /// @
    let adjacencyList (AdjacencyMap m) : ('a * 'a seq) seq =
        m |> Map.toSeq |> Seq.map (fun (k, v) -> k, v |> Set.toSeq)

    /// The /preset/ of an element @x@ is the set of its /direct predecessors/.
    /// Complexity: /O(n * log(n))/ time and /O(n)/ memory.
    ///
    /// @
    /// preSet x 'empty'      == Set.'Set.empty'
    /// preSet x ('vertex' x) == Set.'Set.empty'
    /// preSet 1 ('edge' 1 2) == Set.'Set.empty'
    /// preSet y ('edge' x y) == Set.'Set.fromList' [x]
    /// @
    let preSet (v : 'a) (AdjacencyMap m) : 'a Set =
        let p (_, set) = set |> Set.contains v
        m |> Map.toSeq |> Seq.filter p |> Seq.map fst |> Set.ofSeq

    /// The /postset/ of a vertex is the set of its /direct successors/.
    /// Complexity: /O(log(n))/ time and /O(1)/ memory.
    ///
    /// @
    /// postSet x 'empty'      == Set.'Set.empty'
    /// postSet x ('vertex' x) == Set.'Set.empty'
    /// postSet x ('edge' x y) == Set.'Set.fromList' [y]
    /// postSet 2 ('edge' 1 2) == Set.'Set.empty'
    /// @
    let postSet (v : 'a) (AdjacencyMap m) : 'a Set =
        defaultArg (Map.tryFind v m) Set.empty

    /// The /path/ on a list of vertices.
    /// Complexity: /O((n + m) * log(n))/ time and /O(n + m)/ memory.
    ///
    /// @
    /// path []        == 'empty'
    /// path [x]       == 'vertex' x
    /// path [x,y]     == 'edge' x y
    /// path . 'reverse' == 'transpose' . path
    /// @
    let path (xs : 'a list) : 'a AdjacencyMap =
        match xs with
        | [] -> AdjacencyMap.empty
        | [x] -> AdjacencyMap.vertex x
        | (_::ys) -> edges (List.zip xs ys)

    /// The /circuit/ on a list of vertices.
    /// Complexity: /O((n + m) * log(n))/ time and /O(n + m)/ memory.
    ///
    /// @
    /// circuit []        == 'empty'
    /// circuit [x]       == 'edge' x x
    /// circuit [x,y]     == 'edges' [(x,y), (y,x)]
    /// circuit . 'reverse' == 'transpose' . circuit
    /// @
    let circuit (vs : 'a list) : 'a AdjacencyMap =
        match vs with
        | [] -> AdjacencyMap.empty
        | x::_ -> vs @ [x] |> path

    /// The /clique/ on a list of vertices.
    /// Complexity: /O((n + m) * log(n))/ time and /O(n + m)/ memory.
    ///
    /// @
    /// clique []         == 'empty'
    /// clique [x]        == 'vertex' x
    /// clique [x,y]      == 'edge' x y
    /// clique [x,y,z]    == 'edges' [(x,y), (x,z), (y,z)]
    /// clique (xs ++ ys) == 'connect' (clique xs) (clique ys)
    /// clique . 'reverse'  == 'transpose' . clique
    /// @
    let clique (vs : 'a list) : 'a AdjacencyMap =
        let rec go =
            function
            | [] -> ([], Set.empty)
            | x::xs -> let (res, set) = go xs in (x, set) :: res, Set.add x set
        vs |> go |> fst |> AdjacencyMap.fromAdjacencySets

    /// The /biclique/ on two lists of vertices.
    /// Complexity: /O(n * log(n) + m)/ time and /O(n + m)/ memory.
    ///
    /// @
    /// biclique []      []      == 'empty'
    /// biclique [x]     []      == 'vertex' x
    /// biclique []      [y]     == 'vertex' y
    /// biclique [x1,x2] [y1,y2] == 'edges' [(x1,y1), (x1,y2), (x2,y1), (x2,y2)]
    /// biclique xs      ys      == 'connect' ('vertices' xs) ('vertices' ys)
    /// @
    let biclique (xs : 'a seq) (ys : 'a seq) : 'a AdjacencyMap =
        let x = xs |> Set.ofSeq
        let y = ys |> Set.ofSeq
        let adjacent v = if Set.contains v x then y else Set.empty
        (Set.union x y) |> Map.fromSet adjacent |> AdjacencyMap

    /// TODO: Optimise.
    /// The /star/ formed by a centre vertex connected to a list of leaves.
    /// Complexity: /O((n + m) * log(n))/ time and /O(n + m)/ memory.
    ///
    /// @
    /// star x []    == 'vertex' x
    /// star x [y]   == 'edge' x y
    /// star x [y,z] == 'edges' [(x,y), (x,z)]
    /// star x ys    == 'connect' ('vertex' x) ('vertices' ys)
    /// @
    let star (x : 'a) (ys : 'a list) : 'a AdjacencyMap =
        match ys with
        | [] -> AdjacencyMap.vertex x
        | _ -> AdjacencyMap.connect (AdjacencyMap.vertex x) (vertices ys)

    /// The /stars/ formed by overlaying a list of 'star's. An inverse of
    /// 'adjacencyList'.
    /// Complexity: /O(L * log(n))/ time, memory and size, where /L/ is the total
    /// size of the input.
    ///
    /// @
    /// stars []                      == 'empty'
    /// stars [(x, [])]               == 'vertex' x
    /// stars [(x, [y])]              == 'edge' x y
    /// stars [(x, ys)]               == 'star' x ys
    /// stars                         == 'overlays' . map (uncurry 'star')
    /// stars . 'adjacencyList'         == id
    /// 'overlay' (stars xs) (stars ys) == stars (xs ++ ys)
    /// @
    let stars (stars : ('a * 'a list) seq) : 'a AdjacencyMap =
        stars |> Seq.map (fun (v, vs) -> v, vs |> Set.ofList) |> AdjacencyMap.fromAdjacencySets

    /// The /tree graph/ constructed from a given 'Tree' data structure.
    /// Complexity: /O((n + m) * log(n))/ time and /O(n + m)/ memory.
    ///
    /// @
    /// tree (Node x [])                                         == 'vertex' x
    /// tree (Node x [Node y [Node z []]])                       == 'path' [x,y,z]
    /// tree (Node x [Node y [], Node z []])                     == 'star' x [y,z]
    /// tree (Node 1 [Node 2 [], Node 3 [Node 4 [], Node 5 []]]) == 'edges' [(1,2), (1,3), (3,4), (3,5)]
    /// @
    let rec tree (tree : 'a Tree) : 'a AdjacencyMap =
        match tree.SubForest with
        | [] -> AdjacencyMap.vertex tree.RootLabel
        | f ->
            AdjacencyMap.overlay
                (f |> List.map (fun t -> t.RootLabel) |> star tree.RootLabel)
                (f |> List.filter (fun t -> t.SubForest |> List.isEmpty |> not) |> forest)

    // The /forest graph/ constructed from a given 'Forest' data structure.
    // Complexity: /O((n + m) * log(n))/ time and /O(n + m)/ memory.
    //
    // @
    // forest []                                                  == 'empty'
    // forest [x]                                                 == 'tree' x
    // forest [Node 1 [Node 2 [], Node 3 []], Node 4 [Node 5 []]] == 'edges' [(1,2), (1,3), (4,5)]
    // forest                                                     == 'overlays' . map 'tree'
    // @
    and forest (f : 'a Forest) : 'a AdjacencyMap =
        f |> List.map tree |> overlays

    /// Remove a vertex from a given graph.
    /// Complexity: /O(n*log(n))/ time.
    ///
    /// @
    /// removeVertex x ('vertex' x)       == 'empty'
    /// removeVertex 1 ('vertex' 2)       == 'vertex' 2
    /// removeVertex x ('edge' x x)       == 'empty'
    /// removeVertex 1 ('edge' 1 2)       == 'vertex' 2
    /// removeVertex x . removeVertex x == removeVertex x
    /// @
    let removeVertex (v : 'a) (AdjacencyMap m) : 'a AdjacencyMap =
        m |> Map.remove v |> Map.map (fun _ s -> s |> Set.remove v) |> AdjacencyMap

    /// Remove an edge from a given graph.
    /// Complexity: /O(log(n))/ time.
    ///
    /// @
    /// removeEdge x y ('edge' x y)       == 'vertices' [x,y]
    /// removeEdge x y . removeEdge x y == removeEdge x y
    /// removeEdge x y . 'removeVertex' x == 'removeVertex' x
    /// removeEdge 1 1 (1 * 1 * 2 * 2)  == 1 * 2 * 2
    /// removeEdge 1 2 (1 * 1 * 2 * 2)  == 1 * 1 + 2 * 2
    /// @
    let removeEdge (x : 'a) (y : 'a) (AdjacencyMap m) : 'a AdjacencyMap =
        m |> Map.adjust (Set.remove y) x |> AdjacencyMap

    /// Transform a graph by applying a function to each of its vertices. This is
    /// similar to @Functor@'s 'fmap' but can be used with non-fully-parametric
    /// 'AdjacencyMap'.
    /// Complexity: /O((n + m) * log(n))/ time.
    ///
    /// @
    /// gmap f 'empty'      == 'empty'
    /// gmap f ('vertex' x) == 'vertex' (f x)
    /// gmap f ('edge' x y) == 'edge' (f x) (f y)
    /// gmap id           == id
    /// gmap f . gmap g   == gmap (f . g)
    /// @
    let gmap (f : 'a -> 'b) (AdjacencyMap m) : 'b AdjacencyMap =
        m |> Map.mapKeysWith Set.union f |> Map.map (fun _ v -> Set.map f v) |> AdjacencyMap

    /// The function @'replaceVertex' x y@ replaces vertex @x@ with vertex @y@ in a
    /// given 'AdjacencyMap'. If @y@ already exists, @x@ and @y@ will be merged.
    /// Complexity: /O((n + m) * log(n))/ time.
    ///
    /// @
    /// replaceVertex x x            == id
    /// replaceVertex x y ('vertex' x) == 'vertex' y
    /// replaceVertex x y            == 'mergeVertices' (== x) y
    /// @
    let replaceVertex (u : 'a) (v : 'a) (am : 'a AdjacencyMap) : 'a AdjacencyMap =
        gmap (fun w -> if w = u then v else w) am

    /// Merge vertices satisfying a given predicate into a given vertex.
    /// Complexity: /O((n + m) * log(n))/ time, assuming that the predicate takes
    /// /O(1)/ to be evaluated.
    ///
    /// @
    /// mergeVertices (const False) x    == id
    /// mergeVertices (== x) y           == 'replaceVertex' x y
    /// mergeVertices even 1 (0 * 2)     == 1 * 1
    /// mergeVertices odd  1 (3 + 4 * 5) == 4 * 1
    /// @
    let mergeVertices (p : 'a -> bool) (v : 'a) (am : 'a AdjacencyMap) : 'a AdjacencyMap =
        gmap (fun u -> if p u then v else u) am

    /// Transpose a given graph.
    /// Complexity: /O(m * log(n))/ time, /O(n + m)/ memory.
    ///
    /// @
    /// transpose 'empty'       == 'empty'
    /// transpose ('vertex' x)  == 'vertex' x
    /// transpose ('edge' x y)  == 'edge' y x
    /// transpose . transpose == id
    /// 'edgeList' . transpose  == 'Data.List.sort' . map 'Data.Tuple.swap' . 'edgeList'
    /// @
    let transpose (AdjacencyMap m) : 'a AdjacencyMap =
        let combine s v es = Map.unionWith Set.union (Map.fromSet (fun _ -> Set.singleton v) es) s
        let vs = Map.fromSet (fun _ -> Set.empty) (Map.keysSet m)
        m |> Map.fold combine vs |> AdjacencyMap

    //{-# RULES
    //"transpose/empty"    transpose empty = empty
    //"transpose/vertex"   forall x. transpose (vertex x) = vertex x
    //"transpose/overlay"  forall g1 g2. transpose (overlay g1 g2) = overlay (transpose g1) (transpose g2)
    //"transpose/connect"  forall g1 g2. transpose (connect g1 g2) = connect (transpose g2) (transpose g1)

    //"transpose/overlays" forall xs. transpose (overlays xs) = overlays (map transpose xs)
    //"transpose/connects" forall xs. transpose (connects xs) = connects (reverse (map transpose xs))

    //"transpose/vertices" forall xs. transpose (vertices xs) = vertices xs
    //"transpose/clique"   forall xs. transpose (clique xs)   = clique (reverse xs)
    // #-}

    /// Construct the /induced subgraph/ of a given graph by removing the
    /// vertices that do not satisfy a given predicate.
    /// Complexity: /O(m)/ time, assuming that the predicate takes /O(1)/ to
    /// be evaluated.
    ///
    /// @
    /// induce (const True ) x      == x
    /// induce (const False) x      == 'empty'
    /// induce (/= x)               == 'removeVertex' x
    /// induce p . induce q         == induce (\\x -> p x && q x)
    /// 'isSubgraphOf' (induce p x) x == True
    /// @
    let induce (p : 'a -> bool) (AdjacencyMap m) : 'a AdjacencyMap =
        m |> Map.filter (fun k _ -> p k) |> Map.map (fun k v -> v |> Set.filter p) |> AdjacencyMap
