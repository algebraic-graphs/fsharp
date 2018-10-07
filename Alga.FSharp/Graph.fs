namespace Alga.FSharp

open Alga.FSharp.Internal
open Alga.FSharp.AdjacencyMap.Internal

(*
Module     : Algebra.Graph
Copyright  : (c) Andrey Mokhov 2016-2018
License    : MIT (see the file LICENSE)
Maintainer : andrey.mokhov@gmail.com
Stability  : experimental

__Alga__ is a library for algebraic construction and manipulation of graphs
in Haskell. See <https://github.com/snowleopard/alga-paper this paper> for the
motivation behind the library, the underlying theory, and implementation details.

This module defines the core data type 'Graph' and associated algorithms.
For graphs that are known to be /non-empty/ at compile time, see
"Algebra.Graph.NonEmpty". 'Graph' is an instance of type classes defined in
modules "Algebra.Graph.Class" and "Algebra.Graph.HigherKinded.Class", which
can be used for polymorphic graph construction and manipulation.

The 'Graph' data type is a deep embedding of the core graph construction
primitives 'empty', 'vertex', 'overlay' and 'connect'. We define a 'Num'
instance as a convenient notation for working with graphs:

    > 0           == Vertex 0
    > 1 + 2       == Overlay (Vertex 1) (Vertex 2)
    > 1 * 2       == Connect (Vertex 1) (Vertex 2)
    > 1 + 2 * 3   == Overlay (Vertex 1) (Connect (Vertex 2) (Vertex 3))
    > 1 * (2 + 3) == Connect (Vertex 1) (Overlay (Vertex 2) (Vertex 3))

The 'Eq' instance is currently implemented using the 'AM.AdjacencyMap' as the
/canonical graph representation/ and satisfies all axioms of algebraic graphs:

    * 'overlay' is commutative and associative:

        >       x + y == y + x
        > x + (y + z) == (x + y) + z

    * 'connect' is associative and has 'empty' as the identity:

        >   x * empty == x
        >   empty * x == x
        > x * (y * z) == (x * y) * z

    * 'connect' distributes over 'overlay':

        > x * (y + z) == x * y + x * z
        > (x + y) * z == x * z + y * z

    * 'connect' can be decomposed:

        > x * y * z == x * y + x * z + y * z

The following useful theorems can be proved from the above set of axioms.

    * 'overlay' has 'empty' as the identity and is idempotent:

        >   x + empty == x
        >   empty + x == x
        >       x + x == x

    * Absorption and saturation of 'connect':

        > x * y + x + y == x * y
        >     x * x * x == x * x

When specifying the time and memory complexity of graph algorithms, /n/ will
denote the number of vertices in the graph, /m/ will denote the number of
edges in the graph, and /s/ will denote the /size/ of the corresponding
'Graph' expression. For example, if @g@ is a 'Graph' then /n/, /m/ and /s/ can
be computed as follows:

@n == 'vertexCount' g
m == 'edgeCount' g
s == 'size' g@

Note that 'size' is slightly different from the 'length' method of the
'Foldable' type class, as the latter does not count 'empty' leaves of the
expression:

@'length' 'empty'           == 0
'size'   'empty'           == 1
'length' ('vertex' x)      == 1
'size'   ('vertex' x)      == 1
'length' ('empty' + 'empty') == 0
'size'   ('empty' + 'empty') == 2@

The 'size' of any graph is positive, and the difference @('size' g - 'length' g)@
corresponds to the number of occurrences of 'empty' in an expression @g@.

Converting a 'Graph' to the corresponding 'AM.AdjacencyMap' takes /O(s + m * log(m))/
time and /O(s + m)/ memory. This is also the complexity of the graph equality test,
because it is currently implemented by converting graph expressions to canonical
representations based on adjacency maps.
*)

type 'a Graph =
| Empty
| Vertex of 'a
| Overlay of 'a Graph * 'a Graph
| Connect of 'a Graph * 'a Graph
with
    static member Zero : 'a Graph = Empty
    static member (+) (x : 'a Graph, y : 'a Graph) = Overlay (x, y)
    static member (*) (x : 'a Graph, y : 'a Graph) = Connect (x, y)

[<RequireQualifiedAccess>]
module Graph =

    /// Construct the /empty graph/. An alias for the constructor 'Empty'.
    /// Complexity: /O(1)/ time, memory and size.
    ///
    /// @
    /// 'isEmpty'     empty == True
    /// 'hasVertex' x empty == False
    /// 'vertexCount' empty == 0
    /// 'edgeCount'   empty == 0
    /// 'size'        empty == 1
    /// @
    let empty : 'a Graph =
        Empty

    /// Construct the graph comprising /a single isolated vertex/. An alias for the
    /// constructor 'Vertex'.
    /// Complexity: /O(1)/ time, memory and size.
    ///
    /// @
    /// 'isEmpty'     (vertex x) == False
    /// 'hasVertex' x (vertex x) == True
    /// 'vertexCount' (vertex x) == 1
    /// 'edgeCount'   (vertex x) == 0
    /// 'size'        (vertex x) == 1
    /// @
    let vertex (a : 'a) : 'a Graph =
        Vertex a

    /// /Overlay/ two graphs. An alias for the constructor 'Overlay'. This is a
    /// commutative, associative and idempotent operation with the identity 'empty'.
    /// Complexity: /O(1)/ time and memory, /O(s1 + s2)/ size.
    ///
    /// @
    /// 'isEmpty'     (overlay x y) == 'isEmpty'   x   && 'isEmpty'   y
    /// 'hasVertex' z (overlay x y) == 'hasVertex' z x || 'hasVertex' z y
    /// 'vertexCount' (overlay x y) >= 'vertexCount' x
    /// 'vertexCount' (overlay x y) <= 'vertexCount' x + 'vertexCount' y
    /// 'edgeCount'   (overlay x y) >= 'edgeCount' x
    /// 'edgeCount'   (overlay x y) <= 'edgeCount' x   + 'edgeCount' y
    /// 'size'        (overlay x y) == 'size' x        + 'size' y
    /// 'vertexCount' (overlay 1 2) == 2
    /// 'edgeCount'   (overlay 1 2) == 0
    /// @
    let overlay (x : 'a Graph) (y : 'a Graph) : 'a Graph =
        Overlay (x, y)

    /// /Connect/ two graphs. An alias for the constructor 'Connect'. This is an
    /// associative operation with the identity 'empty', which distributes over
    /// 'overlay' and obeys the decomposition axiom.
    /// Complexity: /O(1)/ time and memory, /O(s1 + s2)/ size. Note that the number
    /// of edges in the resulting graph is quadratic with respect to the number of
    /// vertices of the arguments: /m = O(m1 + m2 + n1 * n2)/.
    ///
    /// @
    /// 'isEmpty'     (connect x y) == 'isEmpty'   x   && 'isEmpty'   y
    /// 'hasVertex' z (connect x y) == 'hasVertex' z x || 'hasVertex' z y
    /// 'vertexCount' (connect x y) >= 'vertexCount' x
    /// 'vertexCount' (connect x y) <= 'vertexCount' x + 'vertexCount' y
    /// 'edgeCount'   (connect x y) >= 'edgeCount' x
    /// 'edgeCount'   (connect x y) >= 'edgeCount' y
    /// 'edgeCount'   (connect x y) >= 'vertexCount' x * 'vertexCount' y
    /// 'edgeCount'   (connect x y) <= 'vertexCount' x * 'vertexCount' y + 'edgeCount' x + 'edgeCount' y
    /// 'size'        (connect x y) == 'size' x        + 'size' y
    /// 'vertexCount' (connect 1 2) == 2
    /// 'edgeCount'   (connect 1 2) == 1
    /// @
    let connect (x : 'a Graph) (y : 'a Graph) : 'a Graph =
        Connect (x, y)

    /// Construct the graph comprising /a single edge/.
    /// Complexity: /O(1)/ time, memory and size.
    ///
    /// @
    /// edge x y               == 'connect' ('vertex' x) ('vertex' y)
    /// 'hasEdge' x y (edge x y) == True
    /// 'edgeCount'   (edge x y) == 1
    /// 'vertexCount' (edge 1 1) == 1
    /// 'vertexCount' (edge 1 2) == 2
    /// @
    let edge (x : 'a) (y : 'a) : 'a Graph =
        connect (vertex x) (vertex y)

    /// Auxiliary function, similar to 'mconcat'.
    let concatg (f : 'a Graph -> 'a Graph -> 'a Graph) (gs : 'a Graph seq) : 'a Graph =
        gs |> Seq.fold f empty

    /// Overlay a given list of graphs.
    /// Complexity: /O(L)/ time and memory, and /O(S)/ size, where /L/ is the length
    /// of the given list, and /S/ is the sum of sizes of the graphs in the list.
    ///
    /// @
    /// overlays []        == 'empty'
    /// overlays [x]       == x
    /// overlays [x,y]     == 'overlay' x y
    /// overlays           == 'foldr' 'overlay' 'empty'
    /// 'isEmpty' . overlays == 'all' 'isEmpty'
    /// @
    let overlays (gs : 'a Graph seq) : 'a Graph =
        gs |> concatg overlay

    /// Construct the graph comprising a given list of isolated vertices.
    /// Complexity: /O(L)/ time, memory and size, where /L/ is the length of the
    /// given list.
    ///
    /// @
    /// vertices []            == 'empty'
    /// vertices [x]           == 'vertex' x
    /// 'hasVertex' x . vertices == 'elem' x
    /// 'vertexCount' . vertices == 'length' . 'Data.List.nub'
    /// 'vertexSet'   . vertices == Set.'Set.fromList'
    /// @
    let vertices (vs : 'a seq) : 'a Graph =
        vs |> Seq.map vertex |> overlays

    /// Construct the graph from a list of edges.
    /// Complexity: /O(L)/ time, memory and size, where /L/ is the length of the
    /// given list.
    ///
    /// @
    /// edges []          == 'empty'
    /// edges [(x,y)]     == 'edge' x y
    /// 'edgeCount' . edges == 'length' . 'Data.List.nub'
    /// @
    let edges (es : ('a * 'a) seq) : 'a Graph =
        es |> Seq.map ((<||) edge) |> overlays

    /// Connect a given list of graphs.
    /// Complexity: /O(L)/ time and memory, and /O(S)/ size, where /L/ is the length
    /// of the given list, and /S/ is the sum of sizes of the graphs in the list.
    ///
    /// @
    /// connects []        == 'empty'
    /// connects [x]       == x
    /// connects [x,y]     == 'connect' x y
    /// connects           == 'foldr' 'connect' 'empty'
    /// 'isEmpty' . connects == 'all' 'isEmpty'
    /// @
    let connects (gs : 'a Graph seq) : 'a Graph =
        gs |> concatg connect

    /// Generalised 'Graph' folding: recursively collapse a 'Graph' by applying
    /// the provided functions to the leaves and internal nodes of the expression.
    /// The order of arguments is: empty, vertex, overlay and connect.
    /// Complexity: /O(s)/ applications of given functions. As an example, the
    /// complexity of 'size' is /O(s)/, since all functions have cost /O(1)/.
    ///
    /// @
    /// foldg 'empty' 'vertex'        'overlay' 'connect'        == id
    /// foldg 'empty' 'vertex'        'overlay' (flip 'connect') == 'transpose'
    /// foldg []    return        (++)    (++)           == 'Data.Foldable.toList'
    /// foldg 0     (const 1)     (+)     (+)            == 'Data.Foldable.length'
    /// foldg 1     (const 1)     (+)     (+)            == 'size'
    /// foldg True  (const False) (&&)    (&&)           == 'isEmpty'
    /// @
    let rec foldg (e : 'b) (v : 'a -> 'b) (o : 'b -> 'b -> 'b) (c : 'b -> 'b -> 'b) (g : 'a Graph) : 'b =
        let go = foldg e v o c
        match g with
        | Empty -> e
        | Vertex x -> v x
        | Overlay (x, y) -> o (go x) (go y)
        | Connect (x, y) -> c (go x) (go y)

    let rec map (f : 'a -> 'b) (g : 'a Graph) : 'b Graph =
        match g with
        | Empty -> Empty
        | Vertex a -> Vertex (f a)
        | Overlay (g1, g2) -> Overlay (map f g1, map f g2)
        | Connect (g1, g2) -> Connect (map f g1, map f g2)

    let bind (g : 'a Graph) (f : 'a -> 'b Graph) : 'b Graph =
        foldg Empty f overlay connect g

    let rec toList (g : 'a Graph) : 'a list =
        match g with
        | Empty -> []
        | Vertex a -> [a]
        | Overlay (g1, g2) -> toList g1 @ toList g2
        | Connect (g1, g2) -> toList g1 @ toList g2

    /// | Check if a graph is empty. A convenient alias for 'null'.
    /// Complexity: /O(s)/ time.
    ///
    /// @
    /// isEmpty 'empty'                       == True
    /// isEmpty ('overlay' 'empty' 'empty')       == True
    /// isEmpty ('vertex' x)                  == False
    /// isEmpty ('removeVertex' x $ 'vertex' x) == True
    /// isEmpty ('removeEdge' x y $ 'edge' x y) == False
    /// @
    let isEmpty (x : 'a Graph) : bool =
        foldg true (fun _ -> false) (&&) (&&) x

    /// The /size/ of a graph, i.e. the number of leaves of the expression
    /// including 'empty' leaves.
    /// Complexity: /O(s)/ time.
    ///
    /// @
    /// size 'empty'         == 1
    /// size ('vertex' x)    == 1
    /// size ('overlay' x y) == size x + size y
    /// size ('connect' x y) == size x + size y
    /// size x             >= 1
    /// size x             >= 'vertexCount' x
    /// @
    let size (x : 'a Graph) : int =
        foldg 1 (fun _ -> 1) (+) (+) x

    /// Check if a graph contains a given vertex. A convenient alias for `elem`.
    /// Complexity: /O(s)/ time.
    ///
    /// @
    /// hasVertex x 'empty'            == False
    /// hasVertex x ('vertex' x)       == True
    /// hasVertex 1 ('vertex' 2)       == False
    /// hasVertex x . 'removeVertex' x == const False
    /// @
    let hasVertex (v : 'a) (g : 'a Graph) : bool =
        foldg false ((=) v) (||) (||) g

    /// Check if a graph contains a given edge.
    /// Complexity: /O(s)/ time.
    ///
    /// @
    /// hasEdge x y 'empty'            == False
    /// hasEdge x y ('vertex' z)       == False
    /// hasEdge x y ('edge' x y)       == True
    /// hasEdge x y . 'removeEdge' x y == const False
    /// hasEdge x y                  == 'elem' (x,y) . 'edgeList'
    /// @
    let hasEdge (s : 'a) (t : 'a) (g : 'a Graph) : bool =

        let rec hit =
            function
            | Empty -> Miss
            | Vertex x -> if x = s then Tail else Miss
            | Overlay (x, y) ->
                match hit x with
                | Miss -> hit y
                | Tail -> max Tail (hit y)
                | Edge -> Edge
            | Connect (x, y) ->
                match hit x with
                | Miss -> hit y
                | Tail -> if hasVertex t y then Edge else Tail
                | Edge -> Edge

        hit g = Edge

    /// The set of vertices of a given graph.
    /// Complexity: /O(s * log(n))/ time and /O(n)/ memory.
    ///
    /// @
    /// vertexSet 'empty'      == Set.'Set.empty'
    /// vertexSet . 'vertex'   == Set.'Set.singleton'
    /// vertexSet . 'vertices' == Set.'Set.fromList'
    /// vertexSet . 'clique'   == Set.'Set.fromList'
    /// @
    let vertexSet (g : 'a Graph) : 'a Set =
        foldg Set.empty Set.singleton Set.union Set.union g

    /// The number of vertices in a graph.
    /// Complexity: /O(s * log(n))/ time.
    ///
    /// @
    /// vertexCount 'empty'      == 0
    /// vertexCount ('vertex' x) == 1
    /// vertexCount            == 'length' . 'vertexList'
    /// @
    let vertexCount (g : 'a Graph) : int =
        g |> vertexSet |> Set.count

    // TODO: This is a very inefficient implementation. Find a way to construct an
    // adjacency map directly, without building intermediate representations for all
    // subgraphs.
    /// Convert a graph to 'AM.AdjacencyMap'.
    let toAdjacencyMap (g : 'a Graph) : 'a AdjacencyMap =
        foldg AdjacencyMap.empty AdjacencyMap.vertex AdjacencyMap.overlay AdjacencyMap.connect g

    /// The number of edges in a graph.
    /// Complexity: /O(s + m * log(m))/ time. Note that the number of edges /m/ of a
    /// graph can be quadratic with respect to the expression size /s/.
    ///
    /// @
    /// edgeCount 'empty'      == 0
    /// edgeCount ('vertex' x) == 0
    /// edgeCount ('edge' x y) == 1
    /// edgeCount            == 'length' . 'edgeList'
    /// @
    let edgeCount (g : 'a Graph) : int =
        g |> toAdjacencyMap |> AdjacencyMap.edgeCount

    /// The sorted list of vertices of a given graph.
    /// Complexity: /O(s * log(n))/ time and /O(n)/ memory.
    ///
    /// @
    /// vertexList 'empty'      == []
    /// vertexList ('vertex' x) == [x]
    /// vertexList . 'vertices' == 'Data.List.nub' . 'Data.List.sort'
    /// @
    let vertexList (g : 'a Graph) : 'a seq =
        g |> vertexSet |> Set.toSeq |> Seq.sort

    /// The sorted list of edges of a graph.
    /// Complexity: /O(s + m * log(m))/ time and /O(m)/ memory. Note that the number of
    /// edges /m/ of a graph can be quadratic with respect to the expression size /s/.
    ///
    /// @
    /// edgeList 'empty'          == []
    /// edgeList ('vertex' x)     == []
    /// edgeList ('edge' x y)     == [(x,y)]
    /// edgeList ('star' 2 [3,1]) == [(2,1), (2,3)]
    /// edgeList . 'edges'        == 'Data.List.nub' . 'Data.List.sort'
    /// edgeList . 'transpose'    == 'Data.List.sort' . map 'Data.Tuple.swap' . edgeList
    /// @
    let edgeList (g : 'a Graph) : ('a * 'a) seq =
        g |> toAdjacencyMap |> AdjacencyMap.edgeList

    /// The set of edges of a given graph.
    /// Complexity: /O(s * log(m))/ time and /O(m)/ memory.
    ///
    /// @
    /// edgeSet 'empty'      == Set.'Set.empty'
    /// edgeSet ('vertex' x) == Set.'Set.empty'
    /// edgeSet ('edge' x y) == Set.'Set.singleton' (x,y)
    /// edgeSet . 'edges'    == Set.'Set.fromList'
    /// @
    let edgeSet (g : 'a Graph) : ('a * 'a) Set =
        g |> toAdjacencyMap |> AdjacencyMap.edgeSet

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
    let adjacencyList (g : 'a Graph) : ('a * 'a seq) seq =
        g |> toAdjacencyMap |> AdjacencyMap.adjacencyList

    /// The /adjacency map/ of a graph: each vertex is associated with a set of its
    /// direct successors.
    /// Complexity: /O(s + m * log(m))/ time. Note that the number of edges /m/ of a
    /// graph can be quadratic with respect to the expression size /s/.
    let adjacencyMap (g : 'a Graph) : Map<'a, 'a Set> =
        g |> toAdjacencyMap |> (fun (AdjacencyMap m) -> m)

    /// The /path/ on a list of vertices.
    /// Complexity: /O(L)/ time, memory and size, where /L/ is the length of the
    /// given list.
    ///
    /// @
    /// path []        == 'empty'
    /// path [x]       == 'vertex' x
    /// path [x,y]     == 'edge' x y
    /// path . 'reverse' == 'transpose' . path
    /// @
    let path (xs : 'a list) : 'a Graph =
        match xs with
        | [] -> empty
        | [x] -> vertex x
        | _::ys -> edges (Seq.zip xs ys)

    //-- The /circuit/ on a list of vertices.
    //-- Complexity: /O(L)/ time, memory and size, where /L/ is the length of the
    //-- given list.
    //--
    //-- @
    //-- circuit []        == 'empty'
    //-- circuit [x]       == 'edge' x x
    //-- circuit [x,y]     == 'edges' [(x,y), (y,x)]
    //-- circuit . 'reverse' == 'transpose' . circuit
    //-- @
    let circuit (xs : 'a list) : 'a Graph =
        match xs with
        | [] -> empty
        | x::_ -> path (xs @ [x])

    /// The /clique/ on a list of vertices.
    /// Complexity: /O(L)/ time, memory and size, where /L/ is the length of the
    /// given list.
    ///
    /// @
    /// clique []         == 'empty'
    /// clique [x]        == 'vertex' x
    /// clique [x,y]      == 'edge' x y
    /// clique [x,y,z]    == 'edges' [(x,y), (x,z), (y,z)]
    /// clique (xs ++ ys) == 'connect' (clique xs) (clique ys)
    /// clique . 'reverse'  == 'transpose' . clique
    /// @
    let clique (xs : 'a seq) : 'a Graph =
        xs |> Seq.map vertex |> connects

    /// The /biclique/ on two lists of vertices.
    /// Complexity: /O(L1 + L2)/ time, memory and size, where /L1/ and /L2/ are the
    /// lengths of the given lists.
    ///
    /// @
    /// biclique []      []      == 'empty'
    /// biclique [x]     []      == 'vertex' x
    /// biclique []      [y]     == 'vertex' y
    /// biclique [x1,x2] [y1,y2] == 'edges' [(x1,y1), (x1,y2), (x2,y1), (x2,y2)]
    /// biclique xs      ys      == 'connect' ('vertices' xs) ('vertices' ys)
    /// @
    let biclique (xs : 'a list) (ys : 'a list) : 'a Graph =
        match xs, ys with
        | _, [] -> vertices xs
        | [], _ -> vertices ys
        | xs, ys -> connect (vertices xs) (vertices ys)

    /// The /star/ formed by a centre vertex connected to a list of leaves.
    /// Complexity: /O(L)/ time, memory and size, where /L/ is the length of the
    /// given list.
    ///
    /// @
    /// star x []    == 'vertex' x
    /// star x [y]   == 'edge' x y
    /// star x [y,z] == 'edges' [(x,y), (x,z)]
    /// star x ys    == 'connect' ('vertex' x) ('vertices' ys)
    /// @
    let star (x : 'a) (ys : 'a list) : 'a Graph =
        connect (vertex x) (vertices ys)

    /// The /stars/ formed by overlaying a list of 'star's. An inverse of
    /// 'adjacencyList'.
    /// Complexity: /O(L)/ time, memory and size, where /L/ is the total size of the
    /// input.
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
    let stars (stars : ('a * 'a list) seq) : 'a Graph =
        stars |> Seq.map ((<||) star) |> overlays

    /// The /tree graph/ constructed from a given 'Tree.Tree' data structure.
    /// Complexity: /O(T)/ time, memory and size, where /T/ is the size of the
    /// given tree (i.e. the number of vertices in the tree).
    ///
    /// @
    /// tree (Node x [])                                         == 'vertex' x
    /// tree (Node x [Node y [Node z []]])                       == 'path' [x,y,z]
    /// tree (Node x [Node y [], Node z []])                     == 'star' x [y,z]
    /// tree (Node 1 [Node 2 [], Node 3 [Node 4 [], Node 5 []]]) == 'edges' [(1,2), (1,3), (3,4), (3,5)]
    /// @
    let rec tree (tree : 'a Tree) : 'a Graph =
        match tree.SubForest with
        | [] -> vertex tree.RootLabel
        | f ->
            overlay
                (star tree.RootLabel (f |> List.map (fun t -> t.RootLabel)))
                (f |> List.filter (fun t -> t.SubForest |> List.isEmpty |> not) |> forest)

    /// The /forest graph/ constructed from a given 'Tree.Forest' data structure.
    /// Complexity: /O(F)/ time, memory and size, where /F/ is the size of the
    /// given forest (i.e. the number of vertices in the forest).
    ///
    /// @
    /// forest []                                                  == 'empty'
    /// forest [x]                                                 == 'tree' x
    /// forest [Node 1 [Node 2 [], Node 3 []], Node 4 [Node 5 []]] == 'edges' [(1,2), (1,3), (4,5)]
    /// forest                                                     == 'overlays' . map 'tree'
    /// @
    and forest (f : 'a Forest) : 'a Graph =
        f |> List.map tree |> overlays

    /// Auxiliary function for 'mesh' and 'torus'
    let pairs (xs : 'a list) : ('a * 'a) list =
        match xs with
        | [] -> []
        | y::ys -> List.zip xs (ys @ [y])

    let rec init (xs : 'a list) : 'a list =
        match xs with
        | [] -> failwith "List was empty"
        | [x] -> []
        | x::xs -> x::(init xs)

    /// Construct a /mesh graph/ from two lists of vertices.
    /// Complexity: /O(L1 * L2)/ time, memory and size, where /L1/ and /L2/ are the
    /// lengths of the given lists.
    ///
    /// @
    /// mesh xs     []   == 'empty'
    /// mesh []     ys   == 'empty'
    /// mesh [x]    [y]  == 'vertex' (x, y)
    /// mesh xs     ys   == 'box' ('path' xs) ('path' ys)
    /// mesh [1..3] "ab" == 'edges' [ ((1,\'a\'),(1,\'b\')), ((1,\'a\'),(2,\'a\')), ((1,\'b\'),(2,\'b\')), ((2,\'a\'),(2,\'b\'))
    ///                           , ((2,\'a\'),(3,\'a\')), ((2,\'b\'),(3,\'b\')), ((3,\'a\'),(3,\'b\')) ]
    /// @
    let mesh (xs : 'a list) (ys : 'b list) : ('a * 'b) Graph =
        match xs, ys with
        | [], _ -> empty
        | _, [] -> empty
        | [x], [y] -> vertex (x, y)
        | _, _ ->
            let lx = List.last xs
            let ly = List.last ys
            let ipxs = init (pairs xs)
            let ipys = init (pairs ys)
            seq {
                for (a1, a2) in ipxs do
                    for (b1, b2) in ipys do
                        yield (a1, b1), [a1, b2 ; a2, b1]
                for (y1, y2) in ipys do
                    yield (lx, y1), [lx, y2]
                for (x1, x2) in ipxs do
                    yield (x1, ly), [x2, ly]
            }
            |> stars

    /// Construct a /torus graph/ from two lists of vertices.
    /// Complexity: /O(L1 * L2)/ time, memory and size, where /L1/ and /L2/ are the
    /// lengths of the given lists.
    ///
    /// @
    /// torus xs    []   == 'empty'
    /// torus []    ys   == 'empty'
    /// torus [x]   [y]  == 'edge' (x,y) (x,y)
    /// torus xs    ys   == 'box' ('circuit' xs) ('circuit' ys)
    /// torus [1,2] "ab" == 'edges' [ ((1,\'a\'),(1,\'b\')), ((1,\'a\'),(2,\'a\')), ((1,\'b\'),(1,\'a\')), ((1,\'b\'),(2,\'b\'))
    ///                           , ((2,\'a\'),(1,\'a\')), ((2,\'a\'),(2,\'b\')), ((2,\'b\'),(1,\'b\')), ((2,\'b\'),(2,\'a\')) ]
    /// @
    let torus (xs : 'a list) (ys : 'b list) : ('a * 'b) Graph =
        seq {
            for (a1, a2) in pairs xs do
                for (b1, b2) in pairs ys do
                    yield (a1, b1), [(a1, b2) ; (a2, b1)]
        }
        |> stars

    /// Construct a /De Bruijn graph/ of a given non-negative dimension using symbols
    /// from a given alphabet.
    /// Complexity: /O(A^(D + 1))/ time, memory and size, where /A/ is the size of the
    /// alphabet and /D/ is the dimension of the graph.
    ///
    /// @
    ///           deBruijn 0 xs               == 'edge' [] []
    /// n > 0 ==> deBruijn n []               == 'empty'
    ///           deBruijn 1 [0,1]            == 'edges' [ ([0],[0]), ([0],[1]), ([1],[0]), ([1],[1]) ]
    ///           deBruijn 2 "0"              == 'edge' "00" "00"
    ///           deBruijn 2 "01"             == 'edges' [ ("00","00"), ("00","01"), ("01","10"), ("01","11")
    ///                                                , ("10","00"), ("10","01"), ("11","10"), ("11","11") ]
    ///           'transpose'   (deBruijn n xs) == 'fmap' 'reverse' $ deBruijn n xs
    ///           'vertexCount' (deBruijn n xs) == ('length' $ 'Data.List.nub' xs)^n
    /// n > 0 ==> 'edgeCount'   (deBruijn n xs) == ('length' $ 'Data.List.nub' xs)^(n + 1)
    /// @
    let deBruijn (len : int) (alphabet : 'a list) : 'a list Graph =
        match len with
        | 0 -> edge [] []
        | _ ->
            let overlaps = [2..len] |> List.map (fun _ -> alphabet)
            let skeleton = overlaps |> List.map (fun s -> Choice1Of2 s, Choice2Of2 s) |> edges
            let expand v = alphabet |> List.map (fun a -> match v with Choice1Of2 left -> [a] @ left | Choice2Of2 right -> right @ [a]) |> vertices
            bind skeleton expand

    /// Construct the /induced subgraph/ of a given graph by removing the
    /// vertices that do not satisfy a given predicate.
    /// Complexity: /O(s)/ time, memory and size, assuming that the predicate takes
    /// /O(1)/ to be evaluated.
    ///
    /// @
    /// induce (const True ) x      == x
    /// induce (const False) x      == 'empty'
    /// induce (/= x)               == 'removeVertex' x
    /// induce p . induce q         == induce (\\x -> p x && q x)
    /// 'isSubgraphOf' (induce p x) x == True
    /// @
    let induce (p : 'a -> bool) (g : 'a Graph) : 'a Graph =
        let k f x y =
            match x, y with
            | _, Empty -> x
            | Empty, _ -> y
            | _ -> f x y
        foldg empty (fun x -> if p x then vertex x else empty) (k overlay) (k connect) g

    /// Remove a vertex from a given graph.
    /// Complexity: /O(s)/ time, memory and size.
    ///
    /// @
    /// removeVertex x ('vertex' x)       == 'empty'
    /// removeVertex 1 ('vertex' 2)       == 'vertex' 2
    /// removeVertex x ('edge' x x)       == 'empty'
    /// removeVertex 1 ('edge' 1 2)       == 'vertex' 2
    /// removeVertex x . removeVertex x == removeVertex x
    /// @
    let removeVertex (v : 'a) (g : 'a Graph) : 'a Graph =
        induce ((<>) v) g

    /// The context of a subgraph comprises the input and output vertices outside
    /// the subgraph that are connected to the vertices inside the subgraph.
    type 'a Context =
        {
            Inputs : 'a list
            Outputs : 'a list
        }

    /// 'Focus' on a specified subgraph.
    let focus (f : 'a -> bool) (g : 'a Graph) : 'a Focus =
        foldg Focus.emptyFocus (Focus.vertexFocus f) Focus.overlayFoci Focus.connectFoci g

    /// Extract the context from a graph 'Focus'. Returns @Nothing@ if the focus
    /// could not be obtained.
    let context (p : 'a -> bool) (g : 'a Graph) : 'a Context option =
        let f = focus p g
        if f.Ok then
            { Inputs = f.Is ; Outputs = f.Os } |> Some
        else
            None

    /// Transpose a given graph.
    /// Complexity: /O(s)/ time, memory and size.
    ///
    /// @
    /// transpose 'empty'       == 'empty'
    /// transpose ('vertex' x)  == 'vertex' x
    /// transpose ('edge' x y)  == 'edge' y x
    /// transpose . transpose == id
    /// transpose ('box' x y)   == 'box' (transpose x) (transpose y)
    /// 'edgeList' . transpose  == 'Data.List.sort' . map 'Data.Tuple.swap' . 'edgeList'
    /// @
    let transpose (g : 'a Graph) : 'a Graph =
        foldg empty vertex overlay (fun x y -> connect y x) g

    /// Filter vertices in a subgraph context.
    let filterContext (s : 'a) (i : 'a -> bool) (o : 'a -> bool) (g : 'a Graph) : 'a Graph =
        let maybe b f a = match a with Some a -> f a | None -> b
        let go (context : 'a Context) =
            let g1 = induce ((<>) s) g
            let g2 = transpose (star s (List.filter i context.Inputs))
            let g3 = star s (List.filter o context.Outputs)
            overlay (overlay g1 g2) g3
        maybe g go (context ((=) s) g)

    /// Remove an edge from a given graph.
    /// Complexity: /O(s)/ time, memory and size.
    ///
    /// @
    /// removeEdge x y ('edge' x y)       == 'vertices' [x,y]
    /// removeEdge x y . removeEdge x y == removeEdge x y
    /// removeEdge x y . 'removeVertex' x == 'removeVertex' x
    /// removeEdge 1 1 (1 * 1 * 2 * 2)  == 1 * 2 * 2
    /// removeEdge 1 2 (1 * 1 * 2 * 2)  == 1 * 1 + 2 * 2
    /// 'size' (removeEdge x y z)         <= 3 * 'size' z
    /// @
    let removeEdge (s : 'a) (t : 'a) (g : 'a Graph) : 'a Graph =
        filterContext s ((<>) s) ((<>) t) g

    /// The function @'replaceVertex' x y@ replaces vertex @x@ with vertex @y@ in a
    /// given 'Graph'. If @y@ already exists, @x@ and @y@ will be merged.
    /// Complexity: /O(s)/ time, memory and size.
    ///
    /// @
    /// replaceVertex x x            == id
    /// replaceVertex x y ('vertex' x) == 'vertex' y
    /// replaceVertex x y            == 'mergeVertices' (== x) y
    /// @
    let replaceVertex (u : 'a) (v : 'a) (g : 'a Graph) : 'a Graph =
        map (fun w -> if w = u then v else w) g

    /// | Merge vertices satisfying a given predicate into a given vertex.
    /// Complexity: /O(s)/ time, memory and size, assuming that the predicate takes
    /// /O(1)/ to be evaluated.
    ///
    /// @
    /// mergeVertices (const False) x    == id
    /// mergeVertices (== x) y           == 'replaceVertex' x y
    /// mergeVertices even 1 (0 * 2)     == 1 * 1
    /// mergeVertices odd  1 (3 + 4 * 5) == 4 * 1
    /// @
    let mergeVertices (p : 'a -> bool) (v : 'a) (g : 'a Graph) : 'a Graph =
        map (fun w -> if p w then v else w) g

    /// Split a vertex into a list of vertices with the same connectivity.
    /// Complexity: /O(s + k * L)/ time, memory and size, where /k/ is the number of
    /// occurrences of the vertex in the expression and /L/ is the length of the
    /// given list.
    ///
    /// @
    /// splitVertex x []                  == 'removeVertex' x
    /// splitVertex x [x]                 == id
    /// splitVertex x [y]                 == 'replaceVertex' x y
    /// splitVertex 1 [0,1] $ 1 * (2 + 3) == (0 + 1) * (2 + 3)
    /// @
    let splitVertex (v : 'a) (us : 'a list) (g : 'a Graph) : 'a Graph =
        bind g (fun w -> if w = v then vertices us else vertex w)

    //{-# RULES
    //"transpose/Empty"    transpose Empty = Empty
    //"transpose/Vertex"   forall x. transpose (Vertex x) = Vertex x
    //"transpose/Overlay"  forall g1 g2. transpose (Overlay g1 g2) = Overlay (transpose g1) (transpose g2)
    //"transpose/Connect"  forall g1 g2. transpose (Connect g1 g2) = Connect (transpose g2) (transpose g1)

    //"transpose/overlays" forall xs. transpose (overlays xs) = overlays (map transpose xs)
    //"transpose/connects" forall xs. transpose (connects xs) = connects (reverse (map transpose xs))

    //"transpose/vertices" forall xs. transpose (vertices xs) = vertices xs
    //"transpose/clique"   forall xs. transpose (clique xs)   = clique (reverse xs)
    // #-}

    let simple (op : 'g -> 'g -> 'g) (x : 'g) (y : 'g) : 'g =
        let z = op x y
        if x = z then
            x
        else if y = z then
            y
        else
            z

    /// Simplify a graph expression. Semantically, this is the identity function,
    /// but it simplifies a given expression according to the laws of the algebra.
    /// The function does not compute the simplest possible expression,
    /// but uses heuristics to obtain useful simplifications in reasonable time.
    /// Complexity: the function performs /O(s)/ graph comparisons. It is guaranteed
    /// that the size of the result does not exceed the size of the given expression.
    ///
    /// @
    /// simplify              == id
    /// 'size' (simplify x)     <= 'size' x
    /// simplify 'empty'       '===' 'empty'
    /// simplify 1           '===' 1
    /// simplify (1 + 1)     '===' 1
    /// simplify (1 + 2 + 1) '===' 1 + 2
    /// simplify (1 * 1 * 1) '===' 1 * 1
    /// @
    let simplify (g : 'a Graph) : 'a Graph =
        foldg empty vertex (simple overlay) (simple connect) g

    /// Compute the /Cartesian product/ of graphs.
    /// Complexity: /O(s1 * s2)/ time, memory and size, where /s1/ and /s2/ are the
    /// sizes of the given graphs.
    ///
    /// @
    /// box ('path' [0,1]) ('path' "ab") == 'edges' [ ((0,\'a\'), (0,\'b\'))
    ///                                       , ((0,\'a\'), (1,\'a\'))
    ///                                       , ((0,\'b\'), (1,\'b\'))
    ///                                       , ((1,\'a\'), (1,\'b\')) ]
    /// @
    /// Up to an isomorphism between the resulting vertex types, this operation
    /// is /commutative/, /associative/, /distributes/ over 'overlay', has singleton
    /// graphs as /identities/ and 'empty' as the /annihilating zero/. Below @~~@
    /// stands for the equality up to an isomorphism, e.g. @(x, ()) ~~ x@.
    ///
    /// @
    /// box x y               ~~ box y x
    /// box x (box y z)       ~~ box (box x y) z
    /// box x ('overlay' y z)   == 'overlay' (box x y) (box x z)
    /// box x ('vertex' ())     ~~ x
    /// box x 'empty'           ~~ 'empty'
    /// 'transpose'   (box x y) == box ('transpose' x) ('transpose' y)
    /// 'vertexCount' (box x y) == 'vertexCount' x * 'vertexCount' y
    /// 'edgeCount'   (box x y) <= 'vertexCount' x * 'edgeCount' y + 'edgeCount' x * 'vertexCount' y
    /// @
    let box (x : 'a Graph) (y : 'b Graph) : ('a * 'b) Graph =
        let xs = y |> toList |> List.map (fun b -> map (fun a -> a, b) x)
        let ys = x |> toList |> List.map (fun a -> map (fun b -> a, b) y)
        xs @ ys |> overlays
