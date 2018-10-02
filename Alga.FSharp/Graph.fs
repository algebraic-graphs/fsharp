namespace Alga.FSharp

open Alga.FSharp.Internal

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
