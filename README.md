# Alga.FSharp

[![Build Status](https://travis-ci.org/nickcowle/alga-fsharp.svg?branch=master)](https://travis-ci.org/nickcowle/alga-fsharp)

Alga.FSharp is an F# port of the [Algebraic graphs library](https://github.com/snowleopard/alga) by [Andrey Mokhov](https://www.ncl.ac.uk/engineering/staff/profile/andreymokhov.html#background). The library is .NET Standard, so can be built and run on Windows, Linux and macOS alike.

## Checkout, building and editing

To work on Alga.FSharp, I recommend using the cross-platform editor [Visual Studio Code](https://code.visualstudio.com/) with the [Ionide](http://ionide.io/) extension.

First, ensure you have the following installed:
* .NET Core (https://www.microsoft.com/net/download)
* Visual Studio Code (https://code.visualstudio.com/)
* From inside Visual Studio Code, the Ionide extension

Now, run the following commands in the terminal:

```
git clone https://github.com/nickcowle/alga-fsharp.git
cd alga-fsharp
dotnet build
code .
```

## Main idea

Consider the following data type, which is defined in the top-level module
[Graph](https://github.com/nickcowle/alga-fsharp/blob/master/Alga.FSharp/Graph.fs)
of the library:

```fsharp
type 'a Graph =
    | Empty
    | Vertex of 'a
    | Overlay of 'a Graph * 'a Graph
    | Connect of 'a Graph * 'a Graph
```

We can give the following semantics to the constructors in terms of the pair **(V, E)** of graph *vertices* and *edges*:

* `Empty` constructs the empty graph **(∅, ∅)**.
* `Vertex x` constructs a graph containing a single vertex, i.e. **({x}, ∅)**.
* `Overlay (x, y)` overlays graphs **(Vx, Ex)** and **(Vy, Ey)** constructing **(Vx ∪ Vy, Ex ∪ Ey)**.
* `Connect (x, y)` connects graphs **(Vx, Ex)** and **(Vy, Ey)** constructing **(Vx ∪ Vy, Ex ∪ Ey ∪ Vx × Vy)**.

The laws associated with the constructors of this type are remarkably similar to those of a [semiring](https://en.wikipedia.org/wiki/Semiring),
so we use `+` and `*` as convenient shortcuts for `Overlay` and `Connect`, respectively:

* (`+`, `Empty`) is an idempotent commutative monoid.
* (`*`, `Empty`) is a monoid.
* `*` distributes over `+`, that is: `x * (y + z) == x * y + x * z` and `(x + y) * z == x * z + y * z`.
* `*` can be decomposed: `x * y * z == x * y + x * z + y * z`.

This algebraic structure corresponds to *unlabelled directed graphs*: every expression represents a graph, and every
graph can be represented by an expression. Other types of graphs (e.g. undirected) can be obtained by modifying the
above set of laws. Algebraic graphs provide a convenient, safe and powerful interface for working with graphs in F#,
and allow the application of equational reasoning for proving the correctness of graph algorithms.
