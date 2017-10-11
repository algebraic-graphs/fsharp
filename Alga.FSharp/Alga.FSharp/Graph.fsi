namespace Alga.FSharp

// Algebraic data type for graphs
type 'a Graph

module Graph =

    // Basic graph construction primitives
    val empty       : 'a Graph
    val vertex      : 'a -> 'a Graph
    val edge        : 'a -> 'a -> 'a Graph
    val overlay     : 'a Graph -> 'a Graph -> 'a Graph
    val connect     : 'a Graph -> 'a Graph -> 'a Graph
    val vertices    : 'a seq -> 'a Graph
    val edges       : ('a * 'a) seq -> 'a Graph
    val overlays    : 'a Graph seq -> 'a Graph
    val connects    : 'a Graph seq -> 'a Graph
    val graph       : 'a seq -> ('a * 'a) seq -> 'a Graph

    // Graph folding
    val foldg : 'b -> ('a -> 'b) -> ('b -> 'b -> 'b) -> ('b -> 'b -> 'b) -> 'a Graph -> 'b

    // Relations on graphs
    val isSubgraphOf : 'a Graph -> 'a Graph -> bool
    val areEqual : 'a Graph -> 'a Graph -> bool

    // Graph properties
    val isEmpty : 'a Graph -> bool
    val size : 'a Graph -> int
    val hasVertex : 'a -> 'a Graph -> bool
    // val hasEdge
    // val vertexCount
    // val edgeCount
    // val vertexList
    // val edgeList
    // val vertexSet
    // val vertexIntSet
    // val edgeSet

    // Standard families of graphs
    // val path
    // val circuit
    // val clique
    // val biclique
    // val star
    // val tree
    // val forest
    // val mesh
    // val torus
    // val deBruijn

    // Graph transformation
    // val removeVertex
    // val removeEdge
    // val replaceVertex
    // val mergeVertices
    // val splitVertex
    // val transpose
    // val induce
    // val simplify

    // Graph composition
    // val box
