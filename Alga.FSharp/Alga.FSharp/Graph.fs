namespace Alga.FSharp

(*
-----------------------------------------------------------------------------
-- |
-- Module     : Algebra.Graph
-- Copyright  : (c) Andrey Mokhov 2016-2017
-- License    : MIT (see the file LICENSE)
-- Maintainer : andrey.mokhov@gmail.com
-- Stability  : experimental
--
-- __Alga__ is a library for algebraic construction and manipulation of graphs
-- in Haskell. See <https://github.com/snowleopard/alga-paper this paper> for the
-- motivation behind the library, the underlying theory, and implementation details.
--
-- This module defines the core data type 'Graph' and associated algorithms.
-- 'Graph' is an instance of type classes defined in modules "Algebra.Graph.Class"
-- and "Algebra.Graph.HigherKinded.Class", which can be used for polymorphic
-- graph construction and manipulation.
--
-----------------------------------------------------------------------------

The 'Graph' datatype is a deep embedding of the core graph construction
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
'Graph' expression. For example, if g is a 'Graph' then /n/, /m/ and /s/ can be
computed as follows:

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
    let empty = Empty

    /// Construct the graph comprising /a single isolated vertex/. An alias for the
    /// constructor 'Vertex'.
    /// Complexity: /O(1)/ time, memory and size.
    ///
    /// @
    /// 'isEmpty'     (vertex x) == False
    /// 'hasVertex' x (vertex x) == True
    /// 'hasVertex' 1 (vertex 2) == False
    /// 'vertexCount' (vertex x) == 1
    /// 'edgeCount'   (vertex x) == 0
    /// 'size'        (vertex x) == 1
    /// @
    let vertex v = Vertex v

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
    let edge v1 v2 = Connect (Vertex v1, Vertex v2)

    /// /Overlay/ two graphs. An alias for the constructor 'Overlay'. This is an
    /// idempotent, commutative and associative operation with the identity 'empty'.
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
    let overlay g1 g2 = Overlay (g1, g2)

    /// /Connect/ two graphs. An alias for the constructor 'Connect'. This is an
    /// associative operation with the identity 'empty', which distributes over the
    /// overlay and obeys the decomposition axiom.
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
    let connect g1 g2 = Connect (g1, g2)

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
    let vertices vs = Seq.fold (fun g -> Vertex >> overlay g) empty vs

    /// Construct the graph from a list of edges.
    /// Complexity: /O(L)/ time, memory and size, where /L/ is the length of the
    /// given list.
    ///
    /// @
    /// edges []          == 'empty'
    /// edges [(x,y)]     == 'edge' x y
    /// 'edgeCount' . edges == 'length' . 'Data.List.nub'
    /// @
    let edges es = Seq.fold (fun g (v1, v2) -> overlay g (edge v1 v2)) empty es

    /// Overlay a given list of graphs.
    /// Complexity: /O(L)/ time and memory, and /O(S)/ size, where /L/ is the length
    /// of the given list, and /S/ is the sum of sizes of the graphs in the list.
    ///
    /// @
    /// overlays []        == 'empty'
    /// overlays [x]       == x
    /// overlays [x,y]     == 'overlay' x y
    /// 'isEmpty' . overlays == 'all' 'isEmpty'
    /// @
    let overlays gs = Seq.fold overlay gs

    /// Connect a given list of graphs.
    /// Complexity: /O(L)/ time and memory, and /O(S)/ size, where /L/ is the length
    /// of the given list, and /S/ is the sum of sizes of the graphs in the list.
    ///
    /// @
    /// connects []        == 'empty'
    /// connects [x]       == x
    /// connects [x,y]     == 'connect' x y
    /// 'isEmpty' . connects == 'all' 'isEmpty'
    /// @
    let connects gs = Seq.fold connect gs

    /// Construct the graph from given lists of vertices /V/ and edges /E/.
    /// The resulting graph contains the vertices /V/ as well as all the vertices
    /// referred to by the edges /E/.
    /// Complexity: /O(|V| + |E|)/ time, memory and size.
    ///
    /// @
    /// graph []  []      == 'empty'
    /// graph [x] []      == 'vertex' x
    /// graph []  [(x,y)] == 'edge' x y
    /// graph vs  es      == 'overlay' ('vertices' vs) ('edges' es)
    /// @
    let graph vs es = overlay (vertices vs) (edges es)

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
    let rec foldg e v o c g =
        let go = foldg e v o c
        match g with
        | Empty -> e
        | Vertex x -> v x
        | Overlay (x, y) -> o (go x) (go y)
        | Connect (x, y) -> c (go x) (go y)

    /// The 'isSubgraphOf' function takes two graphs and returns 'True' if the
    /// first graph is a /subgraph/ of the second.
    /// Complexity: /O(s + m * log(m))/ time. Note that the number of edges /m/ of a
    /// graph can be quadratic with respect to the expression size /s/.
    ///
    /// @
    /// isSubgraphOf 'empty'         x             == True
    /// isSubgraphOf ('vertex' x)    'empty'         == False
    /// isSubgraphOf x             ('overlay' x y) == True
    /// isSubgraphOf ('overlay' x y) ('connect' x y) == True
    /// isSubgraphOf ('path' xs)     ('circuit' xs)  == True
    /// @
    let isSubgraphOf x y = overlay x y = y

    /// Structural equality on graph expressions.
    /// Complexity: /O(s)/ time.
    ///
    /// @
    ///     x === x         == True
    ///     x === x + 'empty' == False
    /// x + y === x + y     == True
    /// 1 + 2 === 2 + 1     == False
    /// x + y === x * y     == False
    /// @
    let areEqual g1 g2 =
        match g1, g2 with
        | Empty, Empty -> true
        | Vertex v1, Vertex v2 -> v1 = v2
        | Overlay (g1, g2), Overlay (g3, g4) -> g1 = g3 && g2 = g4
        | Connect (g1, g2), Connect (g3, g4) -> g1 = g3 && g2 = g4
        | _ -> false

    /// Check if a graph is empty. A convenient alias for 'null'.
    /// Complexity: /O(s)/ time.
    ///
    /// @
    /// isEmpty 'empty'                       == True
    /// isEmpty ('overlay' 'empty' 'empty')       == True
    /// isEmpty ('vertex' x)                  == False
    /// isEmpty ('removeVertex' x $ 'vertex' x) == True
    /// isEmpty ('removeEdge' x y $ 'edge' x y) == False
    /// @
    let rec isEmpty g =
        match g with
        | Empty -> true
        | Vertex _ -> false
        | Overlay (g1, g2) -> isEmpty g1 && isEmpty g2
        | Connect (g1, g2) -> isEmpty g1 && isEmpty g2

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
    let size g = foldg 1 (fun _ -> 1) (+) (+) g

    /// Check if a graph contains a given vertex. A convenient alias for `elem`.
    /// Complexity: /O(s)/ time.
    ///
    /// @
    /// hasVertex x 'empty'            == False
    /// hasVertex x ('vertex' x)       == True
    /// hasVertex x . 'removeVertex' x == const False
    /// @
    let rec hasVertex v g =
        match g with
        | Empty -> false
        | Vertex v' -> v = v'
        | Overlay (g1, g2) -> hasVertex v g1 || hasVertex v g2
        | Connect (g1, g2) -> hasVertex v g1 || hasVertex v g2
